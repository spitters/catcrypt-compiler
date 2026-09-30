/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.GuardedRoute

@[expose] public section

set_option autoImplicit false

/-!
# The guarded scalar semantics of a command with runtime-count loops

`GuardedRoute.semRouteG` gives a command its guarded scalar semantics when the command is
either loop-free or one runtime-count loop under binders. `semG S c` extends it to commands
whose runtime-count loops sit anywhere on the spine of sequences and binders, as the typed
exit front emits them inside its function frame. A loop-free command runs as `semScalar` of
its guarded conversion `ifConvert none S 0 c` (`straightG`); a sequence or binder that
contains a loop runs its parts in turn, the bound list growing as the guarded conversion
grows it (`boundG`); and a runtime-count loop `RForRuntime x b body` runs the trip fold
`guardedTrips x S body` over the natural-number value of its bound `b` at the words of the
environment.

On a loop-free command `semG` is `semScalar` of the guarded conversion
(`semG_of_loopFree`), so it agrees with `semRouteG` on the guarded fragment
(`semG_of_covered`). On a runtime-count loop under binders it is the trip fold from an
environment that agrees with the binders' environment on every source name
(`semG_loopShape`).

## Main results

* `loopFreeB`, `straightG`, `boundG`, `semG` — the loop-free test, the straight semantics,
  the bound list after a command, and the semantics.
* `semG_of_loopFree`, `boundG_of_loopFree` — on a loop-free command, the guarded
  conversion's semantics and bound list.
* `loopFreeB_of_covered`, `semG_of_covered` — the guarded fragment is loop-free, and there
  `semG` is `semRouteG`.
* `semG_loopShape` — a run of a runtime-count loop under binders is the trip fold from an
  environment agreeing with the binders' environment off the lowering temporaries.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.GuardedRouteSeq

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectGuarded
  (ifConvert IsCoveredSCtlGuarded gWrite)
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedLoop (guardedTrips)
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
  (Binder peelBinders bindersEnv)
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedRoute (boundAfter semRouteG
  semRouteG_of_covered)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-! ## 1. The semantics -/

/-- The command has no loop node. -/
def loopFreeB : LowCT → Bool
  | .RSeq a b => loopFreeB a && loopFreeB b
  | .RLetU64Zero _ b => loopFreeB b
  | .RLetZero _ _ b => loopFreeB b
  | .RBlock b => loopFreeB b
  | .RIfNz _ t e => loopFreeB t && loopFreeB e
  | .RForRuntime _ _ _ => false
  | .RFor _ _ _ => false
  | .RWhileNz _ _ => false
  | _ => true

/-- The straight semantics of a loop-free command from the bound list `S`: `semScalar` of its
    guarded conversion. -/
def straightG (S : List String) (c : LowCT) (env : SEnvScalar) : Option SEnvScalar :=
  semScalar (ifConvert none S 0 c).1 env

/-- The natural-number value of a loop bound at the words of an environment. -/
def boundVal (b : SExpr) (env : SEnvScalar) : Nat :=
  b.eval fun s => (envReader env s).toNat

/-- The bound list after a command, from the bound list `S`: the guarded conversion's on a
    loop-free command, composed along sequences and binders that contain a loop, and `S`
    after a runtime-count loop. -/
def boundG : List String → LowCT → List String
  | S, .RSeq a b =>
      if loopFreeB a && loopFreeB b then (ifConvert none S 0 (.RSeq a b)).2.1
      else boundG (boundG S a) b
  | S, .RLetU64Zero x b =>
      if loopFreeB b then (ifConvert none S 0 (.RLetU64Zero x b)).2.1 else boundG (x :: S) b
  | S, .RLetZero x t b =>
      if loopFreeB b then (ifConvert none S 0 (.RLetZero x t b)).2.1 else boundG S b
  | S, .RForRuntime _ _ _ => S
  | S, c => (ifConvert none S 0 c).2.1

/-- **The guarded scalar semantics of a command with runtime-count loops**, from the bound
    list `S`. A loop-free command runs as `straightG`; a sequence or binder containing a loop
    runs its parts in turn, a word binder as the guarded write of `0`; a runtime-count loop
    `RForRuntime x b body` runs `guardedTrips x S body` over `boundVal b`. -/
def semG : List String → LowCT → SEnvScalar → Option SEnvScalar
  | S, .RSeq a b, env =>
      if loopFreeB a && loopFreeB b then straightG S (.RSeq a b) env
      else (semG S a env).bind (semG (boundG S a) b)
  | S, .RLetU64Zero x b, env =>
      if loopFreeB b then straightG S (.RLetU64Zero x b) env
      else (semScalar (gWrite none S x (.SLit 0)) env).bind (semG (x :: S) b)
  | S, .RLetZero x t b, env =>
      if loopFreeB b then straightG S (.RLetZero x t b) env else semG S b env
  | S, .RForRuntime x b body, env => guardedTrips x S body (boundVal b env) env
  | S, c, env => straightG S c env

/-! ## 2. Loop-free commands -/

theorem semG_of_loopFree {c : LowCT} (h : loopFreeB c = true) (S : List String)
    (env : SEnvScalar) : semG S c env = straightG S c env := by
  cases c <;> simp_all [semG, loopFreeB]

theorem boundG_of_loopFree {c : LowCT} (h : loopFreeB c = true) (S : List String) :
    boundG S c = (ifConvert none S 0 c).2.1 := by
  cases c <;> simp_all [boundG, loopFreeB]

theorem loopFreeB_of_covered {c : LowCT} (hc : IsCoveredSCtlGuarded c) : loopFreeB c = true := by
  induction hc <;> simp_all [loopFreeB]

/-- **On the guarded fragment `semG` is `semRouteG`.** -/
theorem semG_of_covered {c : LowCT} (hc : IsCoveredSCtlGuarded c) (S : List String)
    (env : SEnvScalar) : semG S c env = semRouteG S c env := by
  rw [semG_of_loopFree (loopFreeB_of_covered hc), semRouteG_of_covered hc]
  rfl

/-! ## 3. A runtime-count loop under binders -/

/-- Two environments agree off the lowering temporaries. -/
def AgreeNT (e₁ e₂ : SEnvScalar) : Prop := ∀ y, ¬ isTmpName y → e₁ y = e₂ y

theorem agreeNT_upd {e₁ e₂ : SEnvScalar} (h : AgreeNT e₁ e₂) (x : String) {t : CryptoTy}
    (v : ⟦t⟧) : AgreeNT (e₁.upd x v) (e₂.upd x v) := by
  intro y hy
  unfold SEnvScalar.upd
  split
  · rfl
  · exact h y hy

theorem bindersEnv_agreeNT (bs : List Binder) :
    ∀ {e₁ e₂ : SEnvScalar}, AgreeNT e₁ e₂ → AgreeNT (bindersEnv bs e₁) (bindersEnv bs e₂) := by
  induction bs with
  | nil => intro _ _ h; exact h
  | cons b bs ih =>
      intro e₁ e₂ h
      cases b with
      | u64Zero x => exact ih (agreeNT_upd h x _)
      | zero x t => exact ih h

theorem loopFreeB_peel_false {c : LowCT} {bs : List Binder} {x : String} {b : SExpr}
    {body : LowCT} (h : peelBinders c = (bs, .RForRuntime x b body)) : loopFreeB c = false := by
  induction c generalizing bs with
  | RLetU64Zero y c ih =>
      simp only [peelBinders, Prod.mk.injEq] at h
      simp only [loopFreeB]
      exact ih (Prod.ext rfl h.2)
  | RLetZero y t c ih =>
      simp only [peelBinders, Prod.mk.injEq] at h
      simp only [loopFreeB]
      exact ih (Prod.ext rfl h.2)
  | RForRuntime => simp [peelBinders] at h; rfl
  | _ => simp [peelBinders] at h

/-- The guarded write of `0` into a word binder agrees with the binder's update off the
    lowering temporaries. -/
theorem semScalar_gWrite_zero (S : List String) (x : String) (env : SEnvScalar) :
    ∃ env', semScalar (gWrite none S x (.SLit 0)) env = some env' ∧
      AgreeNT env' (env.upd x (t := .sword 64) (0 : BitVec 64)) := by
  refine ⟨_, rfl, ?_⟩
  intro y hy
  unfold SEnvScalar.upd
  split
  · rfl
  · split
    · rename_i heq
      exact absurd ⟨0, heq⟩ hy
    · rfl

/-- **A runtime-count loop under binders.** When the core of `c` under its binders `bs` is
    `RForRuntime x (SVar n) body` and `semG S c` runs from `env` to `e'`, the run is the trip
    fold of `body` from the bound list after the binders, over the word `n` holds, from an
    environment that agrees with the binders' environment off the lowering temporaries. -/
theorem semG_loopShape {c : LowCT} {bs : List Binder} {x n : String} {body : LowCT}
    (h : peelBinders c = (bs, .RForRuntime x (.SVar n) body)) :
    ∀ (S : List String) (env e' : SEnvScalar), semG S c env = some e' →
      ∃ E₀, AgreeNT E₀ (bindersEnv bs env) ∧
        guardedTrips x (boundAfter bs S) body (envReader E₀ n).toNat E₀ = some e' := by
  induction c generalizing bs with
  | RLetU64Zero y b ih =>
      intro S env e' hs
      simp only [peelBinders, Prod.mk.injEq] at h
      obtain ⟨hbs, hb⟩ := h
      subst hbs
      have hlf : loopFreeB b = false := loopFreeB_peel_false (Prod.ext rfl hb)
      simp only [semG, hlf, Bool.false_eq_true, if_false] at hs
      obtain ⟨env1, hw, hag⟩ := semScalar_gWrite_zero S y env
      rw [hw, Option.bind_some] at hs
      obtain ⟨E₀, hE, htr⟩ := ih (Prod.ext rfl hb) (y :: S) env1 e' hs
      refine ⟨E₀, ?_, htr⟩
      intro z hz
      rw [hE z hz]
      exact bindersEnv_agreeNT _ hag z hz
  | RLetZero y t b ih =>
      intro S env e' hs
      simp only [peelBinders, Prod.mk.injEq] at h
      obtain ⟨hbs, hb⟩ := h
      subst hbs
      have hlf : loopFreeB b = false := loopFreeB_peel_false (Prod.ext rfl hb)
      simp only [semG, hlf, Bool.false_eq_true, if_false] at hs
      exact ih (Prod.ext rfl hb) S env e' hs
  | RForRuntime y bnd bd =>
      intro S env e' hs
      simp only [peelBinders, Prod.mk.injEq, LowCT.RForRuntime.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨env, fun _ _ => rfl, hs⟩
  | _ => simp [peelBinders] at h

end CatCrypt.Crypto.SecureCompilation.Dialects.GuardedRouteSeq
