/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.GuardedRoute
public import CatCrypt.Crypto.SecureCompilation.Dialects.CoveredSCtlDecide

@[expose] public section

set_option autoImplicit false

/-!
# The frame of a converted trip body, and the accumulator semantics of the loop route

The loop route runs the converted trip body `T = guardedTripCmd x S body` in two ways: the
route semantics `guardedTrips` runs it on the whole scalar environment of the function, and
the accumulator semantics `accTrips` of the compiled loop runs it on the environment `envOf`
of the body `VarMap`, which binds only the accumulator, the trip index and the invariants.
The two agree when the trip body reads only names it has written or names of the `VarMap`,
keeps the invariants, and writes the accumulator at its type.

`tripFrameB Ty P R c` checks this on the straight commands the guarded conversion produces:
every read is of a name in the tracked list `R`, every written name is added to `R`, no
written name is a lowering temporary or a name of the protected list `P`, and a written name
of the typing list `Ty` is written at its type. Under the check:

* `tripFrameB_frame` — two environments agreeing on `R` run `c` to environments agreeing on
  the list the check returns, which contains `R`;
* `tripFrameB_keep` — a run keeps every protected name and the type of every typed name.

`guardedTrips_accTrips` composes them over the trips: when the whole environment agrees with
`envOf` at the seed on the `VarMap`'s names other than the index, the trip fold runs to an
environment whose accumulator is the value `accTrips` computes.

## Main results

* `frameCleanB`, `frameCleanB_sound` — the expression test of the check.
* `wrOK`, `tripFrameB` — the write test and the frame check.
* `semLowerSExpr_leaves` — a successful expression lowering reads bound words.
* `tripFrameB_frame`, `tripFrameB_keep` — soundness of the check.
* `guardedTrips_accTrips` — the route semantics of the loop computes the accumulator
  semantics of the compiled loop.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.GuardedRouteFrame

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedLt (varsIn)
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedAgree
  (BndP varsInL varsInL_sound upd_self_any upd_ne_any semLowerSExpr_bound)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectGuarded
  (srcNameB srcName_of_srcNameB)
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedLoop (guardedTrips guardedTripCmd)
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedRoute (envOf accOf accTrips)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)

/-! ## 1. The check -/

/-- `srcClean` as a Boolean: variables that are source names (`srcNameB`), literals below
    `2^64`, and the arithmetic, bitwise, shift and high-multiply nodes over such
    expressions. -/
def frameCleanB : SExpr → Bool
  | .SVar x => srcNameB x
  | .SLit n => decide (n < 2 ^ 64)
  | .SAdd a b | .SSub a b | .SMul a b | .SAnd a b | .SXor a b
  | .SShl a b | .SShr a b | .SMulHiU a b => frameCleanB a && frameCleanB b
  | _ => false

theorem frameCleanB_sound : ∀ e : SExpr, frameCleanB e = true → srcClean e
  | .SVar x, h => (srcName_of_srcNameB h).1
  | .SLit n, h => show n < 2 ^ 64 from of_decide_eq_true h
  | .SAdd a b, h | .SSub a b, h | .SMul a b, h | .SAnd a b, h | .SXor a b, h
  | .SShl a b, h | .SShr a b, h | .SMulHiU a b, h => by
      simp only [frameCleanB, Bool.and_eq_true] at h
      exact ⟨frameCleanB_sound a h.1, frameCleanB_sound b h.2⟩

/-- A write of type `t` into `y` is allowed: `y` is a source name (no lowering temporary and
    no guard flag) and not protected, and a type the typing list gives `y` is `t`. -/
def wrOK (Ty : List (String × CryptoTy)) (P : List String) (y : String) (t : CryptoTy) :
    Bool :=
  srcNameB y && !decide (y ∈ P) &&
    match Ty.lookup y with
    | some t' => decide (t' = t)
    | none => true

/-- **The frame check** of a straight command from the tracked list `R`: the list of tracked
    names after the command, or `none`. Reads are of tracked names; writes pass `wrOK` and
    are tracked afterwards. -/
def tripFrameB (Ty : List (String × CryptoTy)) (P : List String) :
    List String → LowCT → Option (List String)
  | R, .RSkip => some R
  | R, .RSeq a b => (tripFrameB Ty P R a).bind fun R₁ => tripFrameB Ty P R₁ b
  | R, .RScalarSet x _ => if wrOK Ty P x (.sword 64) then some (x :: R) else none
  | R, .RLetU64Zero x b =>
      if wrOK Ty P x (.sword 64) then tripFrameB Ty P (x :: R) b else none
  | R, .RScalarSetExpr x e =>
      if wrOK Ty P x (.sword 64) && frameCleanB e && varsInL R e then some (x :: R) else none
  | R, .RArrLoad dst src i =>
      if decide (dst.locDst = .TU64) && wrOK Ty P dst.locVar (.sword 64) &&
          decide (src.locVar ∈ R) && decide (i ∈ R) then some (dst.locVar :: R) else none
  | R, .RArrStore arr i src =>
      if wrOK Ty P arr.locVar (encodeTy arr.locDst) && decide (arr.locVar ∈ R) &&
          decide (i ∈ R) && decide (src.locVar ∈ R) then some R else none
  | R, .RSelect dst sel s0 s1 =>
      if decide (dst.locDst = .TU64) && wrOK Ty P dst.locVar (.sword 64) && decide (sel ∈ R) &&
          decide (s0.locVar ∈ R) && decide (s1.locVar ∈ R) then some (dst.locVar :: R)
      else none
  | _, _ => none

/-! ## 2. Expressions -/

theorem varsIn_and {P Q : String → Prop} :
    ∀ e : SExpr, varsIn P e → varsIn Q e → varsIn (fun s => P s ∧ Q s) e := by
  intro e
  induction e with
  | SVar x => exact fun hp hq => ⟨hp, hq⟩
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb
  | SLt a b iha ihb =>
      exact fun hp hq => ⟨iha hp.1 hq.1, ihb hp.2 hq.2⟩
  | _ => exact fun _ _ => trivial

theorem evalBV_congr_vars (P : String → Prop) (β₁ β₂ : String → BitVec 64)
    (hβ : ∀ s, P s → β₁ s = β₂ s) :
    ∀ e : SExpr, srcClean e → varsIn P e → e.evalBV β₁ = e.evalBV β₂ := by
  intro e
  induction e with
  | SVar x => intro _ hv; exact hβ x hv
  | SLit n => intro _ _; rfl
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      intro hc hv
      simp only [SExpr.evalBV, iha hc.1 hv.1, ihb hc.2 hv.2]
  | _ => intro hc; exact hc.elim

/-- **A successful lowering reads bound words**: every variable of a `srcClean` expression the
    lowering `semLowerSExpr` accepts is a bound word of the environment. -/
theorem semLowerSExpr_leaves :
    ∀ (e : SExpr) (env : SEnvScalar) (cnt : Nat) (r : SEnvScalar × String × Nat),
      semLowerSExpr env cnt e = some r → srcClean e → varsIn (BndP env) e := by
  intro e
  induction e with
  | SVar x =>
      intro env cnt r h _ _
      simp only [semLowerSExpr] at h
      split at h
      · rename_i w hw
        simp [hw]
      · cases h
  | SLit n => intro _ _ _ _ _; trivial
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      intro env cnt r h hc
      simp only [semLowerSExpr] at h
      split at h
      · rename_i e₁ na c₁ ha
        split at h
        · rename_i e₂ nb c₂ hb
          have hva := iha env cnt _ ha hc.1
          have hvb := ihb e₁ c₁ _ hb hc.2
          obtain ⟨e₁', na', c₁', ha', -, hotb, -⟩ := semLowerSExpr_bound a env cnt hc.1 hva
          rw [ha] at ha'
          simp only [Option.some.injEq, Prod.mk.injEq] at ha'
          obtain ⟨rfl, -, -⟩ := ha'
          refine ⟨hva, GuardedLt.varsIn_mono ?_ b hvb⟩
          intro s hs hnt
          have := hotb s (Or.inl hnt)
          simp only [envReadU64, ← this]
          exact hs hnt
        · cases h
      · cases h
  | _ => intro _ _ _ _ hc; exact hc.elim

/-! ## 3. Soundness of the check -/

/-- Two environments agree on the names of `R`. -/
def AgreeOn (R : List String) (e₁ e₂ : SEnvScalar) : Prop := ∀ y ∈ R, e₁ y = e₂ y

theorem agreeOn_upd {R : List String} {e₁ e₂ : SEnvScalar} (h : AgreeOn R e₁ e₂) (x : String)
    {t : CryptoTy} (v : ⟦t⟧) : AgreeOn (x :: R) (e₁.upd x v) (e₂.upd x v) := by
  intro y hy
  by_cases hyx : y = x
  · subst hyx; rw [upd_self_any, upd_self_any]
  · rw [upd_ne_any hyx, upd_ne_any hyx]
    exact h y (List.mem_of_ne_of_mem hyx hy)

theorem agreeOn_upd_mem {R : List String} {e₁ e₂ : SEnvScalar} (h : AgreeOn R e₁ e₂)
    (x : String) {t : CryptoTy} (v : ⟦t⟧) :
    AgreeOn R (e₁.upd x v) (e₂.upd x v) := by
  intro y hy
  exact agreeOn_upd h x v y (List.mem_cons_of_mem _ hy)

theorem wrOK_notTmp {Ty : List (String × CryptoTy)} {P : List String} {y : String}
    {t : CryptoTy} (h : wrOK Ty P y t = true) : ¬ isTmpName y := by
  simp only [wrOK, Bool.and_eq_true] at h
  exact (srcName_of_srcNameB h.1.1).1

theorem wrOK_notP {Ty : List (String × CryptoTy)} {P : List String} {y : String}
    {t : CryptoTy} (h : wrOK Ty P y t = true) : y ∉ P := by
  simp only [wrOK, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
  exact h.1.2

theorem wrOK_ty {Ty : List (String × CryptoTy)} {P : List String} {y : String}
    {t t' : CryptoTy} (h : wrOK Ty P y t = true) (hl : Ty.lookup y = some t') : t' = t := by
  simp only [wrOK, Bool.and_eq_true, hl, decide_eq_true_eq] at h
  exact h.2

/-- **The frame of a checked command.** Two environments agreeing on `R` run a command the
    check accepts from `R` to environments agreeing on the returned list, which contains `R`
    and no lowering temporary. -/
theorem tripFrameB_frame (Ty : List (String × CryptoTy)) (P : List String) :
    ∀ (c : LowCT) (R R' : List String), tripFrameB Ty P R c = some R' →
      (∀ y ∈ R, ¬ isTmpName y) → ∀ (e₁ e₂ e₁' : SEnvScalar), AgreeOn R e₁ e₂ →
      semScalar c e₁ = some e₁' →
      (∀ y ∈ R, y ∈ R') ∧ (∀ y ∈ R', ¬ isTmpName y) ∧
        ∃ e₂', semScalar c e₂ = some e₂' ∧ AgreeOn R' e₁' e₂' := by
  intro c
  induction c with
  | RSkip =>
      intro R R' h hnt e₁ e₂ e₁' hag hs
      simp only [tripFrameB, Option.some.injEq] at h
      subst h
      simp only [semScalar, Option.some.injEq] at hs
      subst hs
      exact ⟨fun _ h => h, hnt, e₂, rfl, hag⟩
  | RSeq a b iha ihb =>
      intro R R' h hnt e₁ e₂ e₁' hag hs
      simp only [tripFrameB] at h
      cases ha : tripFrameB Ty P R a with
      | none => rw [ha] at h; cases h
      | some R₁ =>
          rw [ha, Option.bind_some] at h
          simp only [semScalar] at hs
          cases hsa : semScalar a e₁ with
          | none => rw [hsa] at hs; cases hs
          | some m₁ =>
              rw [hsa, Option.bind_some] at hs
              obtain ⟨hsub₁, hnt₁, m₂, hm₂, hag₁⟩ := iha R R₁ ha hnt e₁ e₂ m₁ hag hsa
              obtain ⟨hsub₂, hnt₂, e₂', he₂', hag₂⟩ := ihb R₁ R' h hnt₁ m₁ m₂ e₁' hag₁ hs
              refine ⟨fun y hy => hsub₂ y (hsub₁ y hy), hnt₂, e₂', ?_, hag₂⟩
              simp only [semScalar, hm₂, Option.bind_some]
              exact he₂'
  | RScalarSet x n =>
      intro R R' h hnt e₁ e₂ e₁' hag hs
      simp only [tripFrameB] at h
      split at h
      · rename_i hw
        cases h
        simp only [semScalar, Option.some.injEq] at hs
        subst hs
        refine ⟨fun y hy => List.mem_cons_of_mem _ hy, ?_, _, rfl, agreeOn_upd hag x _⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact wrOK_notTmp hw
        · exact hnt y hy
      · cases h
  | RLetU64Zero x b ih =>
      intro R R' h hnt e₁ e₂ e₁' hag hs
      simp only [tripFrameB] at h
      split at h
      · rename_i hw
        simp only [semScalar] at hs
        have hnt' : ∀ y ∈ x :: R, ¬ isTmpName y := by
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact wrOK_notTmp hw
          · exact hnt y hy
        obtain ⟨hsub, hnt₂, e₂', he₂', hag₂⟩ :=
          ih (x :: R) R' h hnt' _ _ e₁' (agreeOn_upd hag x _) hs
        exact ⟨fun y hy => hsub y (List.mem_cons_of_mem _ hy), hnt₂, e₂', he₂', hag₂⟩
      · cases h
  | RScalarSetExpr x e =>
      intro R R' h hnt e₁ e₂ e₁' hag hs
      simp only [tripFrameB] at h
      split at h
      · rename_i hw
        cases h
        simp only [Bool.and_eq_true] at hw
        obtain ⟨⟨hw, hcl⟩, hvl⟩ := hw
        have hcl := frameCleanB_sound e hcl
        have hvR : varsIn (· ∈ R) e := varsInL_sound (fun _ h => h) e hvl
        simp only [semScalar] at hs
        split at hs
        · rename_i a₁ nm₁ c₁ hl₁
          cases hs
          have hv₁ := semLowerSExpr_leaves e e₁ 0 _ hl₁ hcl
          have hv₂ : varsIn (BndP e₂) e := by
            refine GuardedLt.varsIn_mono ?_ e (varsIn_and e hvR hv₁)
            intro s ⟨hsR, hsb⟩ hnts
            simp only [envReadU64, ← hag s hsR]
            exact hsb hnts
          obtain ⟨a₁', n₁', k₁', hl₁', -, hotb₁, -⟩ := semLowerSExpr_bound e e₁ 0 hcl hv₁
          rw [hl₁] at hl₁'
          simp only [Option.some.injEq, Prod.mk.injEq] at hl₁'
          obtain ⟨rfl, -, -⟩ := hl₁'
          obtain ⟨a₂, nm₂, c₂, hl₂, -, hotb₂, -⟩ := semLowerSExpr_bound e e₂ 0 hcl hv₂
          have hval : e.evalBV (envReader e₁) = e.evalBV (envReader e₂) := by
            refine evalBV_congr_vars (· ∈ R) _ _ ?_ e hcl hvR
            intro s hs
            simp only [envReader, hag s hs]
          refine ⟨fun y hy => List.mem_cons_of_mem _ hy, ?_,
            a₂.upd x (t := .sword 64) (e.evalBV (envReader e₂)), ?_, ?_⟩
          · intro y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · exact wrOK_notTmp hw
            · exact hnt y hy
          · simp only [semScalar, hl₂]
          · rw [hval]
            refine agreeOn_upd ?_ x _
            intro y hy
            rw [hotb₁ y (Or.inl (hnt y hy)), hotb₂ y (Or.inl (hnt y hy))]
            exact hag y hy
        · cases hs
      · cases h
  | RArrLoad dst src i =>
      intro R R' h hnt e₁ e₂ e₁' hag hs
      simp only [tripFrameB] at h
      split at h
      · rename_i hw
        cases h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
        obtain ⟨⟨⟨hd, hw⟩, hsrc⟩, hi⟩ := hw
        have hsrcE := hag _ hsrc
        have hiE := hag _ hi
        refine ⟨fun y hy => List.mem_cons_of_mem _ hy, ?_, ?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact wrOK_notTmp hw
          · exact hnt y hy
        · simp only [semScalar] at hs ⊢
          rw [← hsrcE, ← hiE]
          split at hs <;> (cases hs; exact ⟨_, rfl, agreeOn_upd hag _ _⟩)
      · cases h
  | RArrStore arr i src =>
      intro R R' h hnt e₁ e₂ e₁' hag hs
      simp only [tripFrameB] at h
      split at h
      · rename_i hw
        cases h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
        obtain ⟨⟨⟨hw, ha⟩, hi⟩, hsrc⟩ := hw
        have haE := hag _ ha
        have hsrcE := hag _ hsrc
        have hiE := hag _ hi
        refine ⟨fun y hy => hy, hnt, ?_⟩
        simp only [semScalar] at hs ⊢
        rw [← haE, ← hsrcE, ← hiE]
        split at hs
        · split at hs <;> (cases hs; exact ⟨_, by simp_all, agreeOn_upd_mem hag _ _⟩)
        · cases hs; exact ⟨_, rfl, agreeOn_upd_mem hag _ _⟩
      · cases h
  | RSelect dst sel s0 s1 =>
      intro R R' h hnt e₁ e₂ e₁' hag hs
      simp only [tripFrameB] at h
      split at h
      · rename_i hw
        cases h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
        obtain ⟨⟨⟨⟨hd, hw⟩, hsel⟩, h0⟩, h1⟩ := hw
        have hselE := hag _ hsel
        have h0E := hag _ h0
        have h1E := hag _ h1
        refine ⟨fun y hy => List.mem_cons_of_mem _ hy, ?_, ?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact wrOK_notTmp hw
          · exact hnt y hy
        · simp only [semScalar] at hs ⊢
          rw [← hselE, ← h0E, ← h1E]
          split at hs <;> (cases hs; exact ⟨_, rfl, agreeOn_upd hag _ _⟩)
      · cases h
  | _ => intro R R' h; simp [tripFrameB] at h

/-- A value of type `t` at `y`. -/
def HasTy (e : SEnvScalar) (y : String) (t : CryptoTy) : Prop := ∃ v : ⟦t⟧, e y = some ⟨t, v⟩

theorem hasTy_upd {e : SEnvScalar} {x y : String} {t t' : CryptoTy} (v : ⟦t'⟧)
    (h : HasTy e y t) (hxy : y = x → t' = t) : HasTy (e.upd x v) y t := by
  by_cases hyx : y = x
  · subst hyx
    obtain rfl := hxy rfl
    exact ⟨v, upd_self_any⟩
  · rw [HasTy, upd_ne_any hyx]; exact h

/-- **A checked command keeps what it does not write.** A run of a command the check accepts
    leaves every protected name that is no lowering temporary unchanged, and keeps the type
    the typing list gives a name that is no lowering temporary. -/
theorem tripFrameB_keep (Ty : List (String × CryptoTy)) (P : List String) :
    ∀ (c : LowCT) (R R' : List String), tripFrameB Ty P R c = some R' →
      ∀ (e e' : SEnvScalar), semScalar c e = some e' →
      (∀ y ∈ P, ¬ isTmpName y → e' y = e y) ∧
        (∀ y t, Ty.lookup y = some t → ¬ isTmpName y → HasTy e y t → HasTy e' y t) := by
  intro c
  induction c with
  | RSkip =>
      intro R R' _ e e' hs
      simp only [semScalar, Option.some.injEq] at hs
      subst hs
      exact ⟨fun _ _ _ => rfl, fun _ _ _ _ h => h⟩
  | RSeq a b iha ihb =>
      intro R R' h e e' hs
      simp only [tripFrameB] at h
      cases ha : tripFrameB Ty P R a with
      | none => rw [ha] at h; cases h
      | some R₁ =>
          rw [ha, Option.bind_some] at h
          simp only [semScalar] at hs
          cases hsa : semScalar a e with
          | none => rw [hsa] at hs; cases hs
          | some m =>
              rw [hsa, Option.bind_some] at hs
              obtain ⟨hp₁, ht₁⟩ := iha R R₁ ha e m hsa
              obtain ⟨hp₂, ht₂⟩ := ihb R₁ R' h m e' hs
              exact ⟨fun y hy hnt => (hp₂ y hy hnt).trans (hp₁ y hy hnt),
                fun y t hl hnt hh => ht₂ y t hl hnt (ht₁ y t hl hnt hh)⟩
  | RScalarSet x n =>
      intro R R' h e e' hs
      simp only [tripFrameB] at h
      split at h
      · rename_i hw
        simp only [semScalar, Option.some.injEq] at hs
        subst hs
        refine ⟨fun y hy _ => upd_ne_any (fun hyx => wrOK_notP hw (hyx ▸ hy)), ?_⟩
        intro y t hl _ hh
        exact hasTy_upd _ hh (fun hyx => (wrOK_ty hw (hyx ▸ hl)).symm)
      · cases h
  | RLetU64Zero x b ih =>
      intro R R' h e e' hs
      simp only [tripFrameB] at h
      split at h
      · rename_i hw
        simp only [semScalar] at hs
        obtain ⟨hp, ht⟩ := ih (x :: R) R' h _ e' hs
        refine ⟨fun y hy hnt => (hp y hy hnt).trans
          (upd_ne_any (fun hyx => wrOK_notP hw (hyx ▸ hy))), ?_⟩
        intro y t hl hnt hh
        exact ht y t hl hnt (hasTy_upd _ hh (fun hyx => (wrOK_ty hw (hyx ▸ hl)).symm))
      · cases h
  | RScalarSetExpr x e₀ =>
      intro R R' h e e' hs
      simp only [tripFrameB] at h
      split at h
      · rename_i hw
        simp only [Bool.and_eq_true] at hw
        obtain ⟨⟨hw, hcl⟩, -⟩ := hw
        have hcl := frameCleanB_sound e₀ hcl
        simp only [semScalar] at hs
        split at hs
        · rename_i a₁ nm₁ c₁ hl₁
          cases hs
          have hv₁ := semLowerSExpr_leaves e₀ e 0 _ hl₁ hcl
          obtain ⟨a₁', n₁', k₁', hl₁', -, hotb, -⟩ := semLowerSExpr_bound e₀ e 0 hcl hv₁
          rw [hl₁] at hl₁'
          simp only [Option.some.injEq, Prod.mk.injEq] at hl₁'
          obtain ⟨rfl, -, -⟩ := hl₁'
          refine ⟨fun y hy hnt => ?_, ?_⟩
          · rw [upd_ne_any (x := x) (y := y) (fun hyx => wrOK_notP hw (hyx ▸ hy))]
            exact hotb y (Or.inl hnt)
          · intro y t hl hnt hh
            refine hasTy_upd _ ?_ (fun hyx => (wrOK_ty hw (hyx ▸ hl)).symm)
            obtain ⟨v, hv⟩ := hh
            exact ⟨v, (hotb y (Or.inl hnt)).trans hv⟩
        · cases hs
      · cases h
  | RArrLoad dst src i =>
      intro R R' h e e' hs
      simp only [tripFrameB] at h
      split at h
      · rename_i hw
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
        obtain ⟨⟨⟨hd, hw⟩, -⟩, -⟩ := hw
        obtain ⟨d, dt⟩ := dst
        simp only [Located.locDst] at hd
        subst hd
        simp only [semScalar, Located.locDst] at hs
        split at hs <;>
        · cases hs
          refine ⟨fun y hy _ => upd_ne_any (fun hyx => wrOK_notP hw (hyx ▸ hy)), ?_⟩
          intro y t hl _ hh
          exact hasTy_upd _ hh (fun hyx => (wrOK_ty hw (hyx ▸ hl)).symm)
      · cases h
  | RArrStore arr i src =>
      intro R R' h e e' hs
      simp only [tripFrameB] at h
      split at h
      · rename_i hw
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
        obtain ⟨⟨⟨hw, -⟩, -⟩, -⟩ := hw
        simp only [semScalar] at hs
        split at hs
        · split at hs <;>
          · cases hs
            refine ⟨fun y hy _ => upd_ne_any (fun hyx => wrOK_notP hw (hyx ▸ hy)), ?_⟩
            intro y t hl _ hh
            exact hasTy_upd _ hh (fun hyx => (wrOK_ty hw (hyx ▸ hl)).symm)
        · cases hs
          refine ⟨fun y hy _ => upd_ne_any (fun hyx => wrOK_notP hw (hyx ▸ hy)), ?_⟩
          intro y t hl _ hh
          exact hasTy_upd _ hh (fun hyx => (wrOK_ty hw (hyx ▸ hl)).symm)
      · cases h
  | RSelect dst sel s0 s1 =>
      intro R R' h e e' hs
      simp only [tripFrameB] at h
      split at h
      · rename_i hw
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
        obtain ⟨⟨⟨⟨hd, hw⟩, -⟩, -⟩, -⟩ := hw
        obtain ⟨d, dt⟩ := dst
        simp only [Located.locDst] at hd
        subst hd
        simp only [semScalar, Located.locDst] at hs
        split at hs <;>
        · cases hs
          refine ⟨fun y hy _ => upd_ne_any (fun hyx => wrOK_notP hw (hyx ▸ hy)), ?_⟩
          intro y t hl _ hh
          exact hasTy_upd _ hh (fun hyx => (wrOK_ty hw (hyx ▸ hl)).symm)
      · cases h
  | _ => intro R R' h; simp [tripFrameB] at h

/-! ## 4. The trips of the loop route -/

theorem mem_map_fst_of_lookup {l : List (String × CryptoTy)} {a : String} {b : CryptoTy}
    (h : l.lookup a = some b) : a ∈ l.map Prod.fst := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
      obtain ⟨p₁, p₂⟩ := p
      by_cases hp : a = p₁
      · subst hp; exact List.mem_cons_self
      · simp only [List.lookup] at h
        have : (a == p₁) = false := by simpa using hp
        rw [this] at h
        exact List.mem_cons_of_mem _ (ih h)

theorem accOf_of_eq {t : CryptoTy} {name : String} {e : SEnvScalar} {a : ⟦t⟧}
    (h : e name = some ⟨t, a⟩) : accOf t name e = some a := by
  simp [accOf, h]

/-- The whole environment `E` agrees with `envOf` of the body `VarMap` at the accumulator `a`,
    the index `0` and the invariants `invsC` on every name of the `VarMap` other than the
    index `x`. -/
def TripInv {accCTy : CryptoTy} {invCTys : Ctx} (vm : VarMap (accCTy :: .sword 64 :: invCTys))
    (x : String) (invsC : Ctxt.Valuation (d := catCryptDialect) invCTys) (E : SEnvScalar)
    (a : ⟦accCTy⟧) : Prop :=
  ∀ s, (vm.lookup s).isSome → s ≠ x → E s = envOf vm (.cons a (.cons (0 : BitVec 64) invsC)) s

/-- **The route semantics of the loop computes the accumulator semantics.** Let the converted
    trip body `T = guardedTripCmd x S body` pass the frame check from the names of the typing
    list `Ty`, which are the names of the body `VarMap` and no lowering temporaries, with the
    accumulator typed at its type and every name of the `VarMap` other than the index and the
    accumulator protected. Let `envOf vm` read the accumulator at `accName` and the index at
    `x`, the other names independently of the index and, off the accumulator, of the
    accumulator. From an environment agreeing with `envOf` at the seed `a₀` off the index,
    `k` trips of `guardedTrips` run to an environment agreeing with `envOf` at the value
    `accTrips` computes for `k` trips. -/
theorem guardedTrips_accTrips {accCTy : CryptoTy} {invCTys : Ctx}
    (vm : VarMap (accCTy :: .sword 64 :: invCTys)) (accName x : String) (S : List String)
    (body : LowCT) (invsC : Ctxt.Valuation (d := catCryptDialect) invCTys)
    (Ty : List (String × CryptoTy)) (P R' : List String)
    (hgate : tripFrameB Ty P (Ty.map Prod.fst) (guardedTripCmd x S body) = some R')
    (hdom : ∀ s, s ∈ Ty.map Prod.fst ↔ (vm.lookup s).isSome)
    (hnt : ∀ s ∈ Ty.map Prod.fst, ¬ isTmpName s)
    (hTyAcc : Ty.lookup accName = some accCTy)
    (hacc : ∀ (a : ⟦accCTy⟧) (t : BitVec 64),
      envOf vm (.cons a (.cons t invsC)) accName = some ⟨accCTy, a⟩)
    (hidx : ∀ (a : ⟦accCTy⟧) (t : BitVec 64),
      envOf vm (.cons a (.cons t invsC)) x = some ⟨.sword 64, t⟩)
    (hindT : ∀ s, s ≠ x → ∀ (a : ⟦accCTy⟧) (t t' : BitVec 64),
      envOf vm (.cons a (.cons t invsC)) s = envOf vm (.cons a (.cons t' invsC)) s)
    (hindA : ∀ s, s ≠ x → s ≠ accName → ∀ (a a' : ⟦accCTy⟧) (t : BitVec 64),
      envOf vm (.cons a (.cons t invsC)) s = envOf vm (.cons a' (.cons t invsC)) s)
    (hP : ∀ s, (vm.lookup s).isSome → s ≠ x → s ≠ accName → s ∈ P) :
    ∀ (k : Nat) (E₀ Eₖ : SEnvScalar) (a₀ : ⟦accCTy⟧), TripInv vm x invsC E₀ a₀ →
      guardedTrips x S body k E₀ = some Eₖ →
      ∃ aₖ, accTrips vm accName (guardedTripCmd x S body) invsC k a₀ = some aₖ ∧
        TripInv vm x invsC Eₖ aₖ := by
  have hAccMem : accName ∈ Ty.map Prod.fst := mem_map_fst_of_lookup hTyAcc
  intro k
  induction k with
  | zero =>
      intro E₀ Eₖ a₀ hinv h
      simp only [guardedTrips, Option.some.injEq] at h
      subst h
      exact ⟨a₀, rfl, hinv⟩
  | succ k ih =>
      intro E₀ E' a₀ hinv h
      simp only [guardedTrips] at h
      cases hk : guardedTrips x S body k E₀ with
      | none => rw [hk] at h; cases h
      | some Eₖ =>
          rw [hk, Option.bind_some] at h
          obtain ⟨aₖ, hak, hinvₖ⟩ := ih E₀ Eₖ a₀ hinv hk
          have hag : AgreeOn (Ty.map Prod.fst)
              (Eₖ.upd x (t := .sword 64) (BitVec.ofNat 64 k))
              (envOf vm (.cons aₖ (.cons (BitVec.ofNat 64 k) invsC))) := by
            intro y hy
            by_cases hyx : y = x
            · subst hyx
              rw [upd_self_any, hidx]
            · rw [upd_ne_any hyx, hinvₖ y ((hdom y).1 hy) hyx, hindT y hyx aₖ 0]
          obtain ⟨hsub, -, e₂', he₂', hag'⟩ :=
            tripFrameB_frame Ty P _ _ R' hgate hnt _ _ E' hag h
          obtain ⟨-, hty₂⟩ := tripFrameB_keep Ty P _ _ R' hgate _ e₂' he₂'
          obtain ⟨hp₁, -⟩ := tripFrameB_keep Ty P _ _ R' hgate _ E' h
          obtain ⟨a', ha'⟩ := hty₂ accName accCTy hTyAcc (hnt _ hAccMem)
            ⟨aₖ, hacc aₖ (BitVec.ofNat 64 k)⟩
          refine ⟨a', ?_, ?_⟩
          · simp only [accTrips, hak, Option.bind_some, he₂']
            exact accOf_of_eq ha'
          · intro s hs hsx
            by_cases hsa : s = accName
            · subst hsa
              rw [hag' s (hsub s hAccMem), ha', hacc a' 0]
            · have hsT : s ∈ Ty.map Prod.fst := (hdom s).2 hs
              rw [hp₁ s (hP s hs hsx hsa) (hnt s hsT), upd_ne_any hsx, hinvₖ s hs hsx,
                hindA s hsx hsa aₖ a' 0]

end CatCrypt.Crypto.SecureCompilation.Dialects.GuardedRouteFrame
