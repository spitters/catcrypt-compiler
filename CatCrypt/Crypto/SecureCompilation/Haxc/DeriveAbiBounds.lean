/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.DeriveBoundsSound
import CatCrypt.Crypto.SecureCompilation.Haxc.CensusCore
import CatCrypt.Crypto.SecureCompilation.Haxc.NFChain

set_option autoImplicit false

/-!
# The bounds of a derived layout lose no source run

`Census.deriveAbi` adds the derived bounds of `DeriveBounds.deriveBounds` to the layout it reads
off an extraction. At every entry state and environment the layout reads off it, a source run
of the extraction to a value satisfies each of these bounds (`DeriveBounds.deriveBounds_hold` at
the table `hax64WExit`): the first conjunct of `AbiLayout.Regions` excludes no such run.

## Main results

* `deriveAbi_consts_noCF` — no constant of a derived layout is a control-flow value.
* `deriveAbi_bounds_hold` — the bounds hold at every run of `denoteSpine` at `hax64WExit`.
* `deriveAbi_bounds_of_haxRuns` — the bounds hold at every run of `haxRuns`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.DeriveBounds

open _root_.Hax (TExpr Value Env)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.Hax (hax64WExit HaxModule)

/-! ## The derived layout -/

/-- No constant of a derived layout is a control-flow value: each is the value of a literal. -/
theorem deriveAbi_consts_noCF {wide : Bool} {consts : List (String × TExpr)} {te : TExpr}
    {σ : AbiLayout} (h : Census.deriveAbi wide consts te = .ok σ) :
    ∀ c ∈ σ.consts, c.2.isControlFlow = false := by
  simp only [Census.deriveAbi, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      intro c hc
      obtain ⟨c0, -, hc0⟩ := List.mem_filterMap.mp hc
      split at hc0
      · obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hc0
        unfold Census.constVal at hv
        split at hv <;> cases hv <;> rfl
      · cases hc0

/-- **The bounds of a derived layout lose no source run.** Let `deriveAbi` read the layout `σ`
    off the extraction `te`. At every entry state `sa` and environment `env` that `σ` reads off
    it (`AbiLayout.EnvOf`), a run of the source reading of `te` (`denoteSpine` at the table
    `hax64WExit` of `haxRuns`) from `env` to a value that is not a control-flow value has each
    register a bound of `σ` names at most its bound: the first conjunct of `AbiLayout.Regions`
    excludes no such run. -/
theorem deriveAbi_bounds_hold {wide : Bool} {consts : List (String × TExpr)} {te : TExpr}
    {σ : AbiLayout} (hσ : Census.deriveAbi wide consts te = .ok σ) {sa : AState} {env : Env}
    (henv : σ.EnvOf sa env) {fuel : Nat} {v : Value} {env' : Env}
    (hrun : (_root_.Hax.InlineLocalClosures.denoteSpine hax64WExit fuel te.erase).run env =
      (.val v, env'))
    (hv : v.isControlFlow = false) : ∀ b ∈ σ.bounds, (sa.regs b.1).toNat ≤ b.2 := by
  rw [Census.deriveAbi_bounds hσ]
  exact deriveBounds_hold siteTable_hax64WExit henv (deriveAbi_consts_noCF hσ) hrun hv

/-- **The bounds of a derived layout hold at every source run of `haxRuns`** of the function
    `te`: `deriveAbi_bounds_hold` through `haxRuns_single`. -/
theorem deriveAbi_bounds_of_haxRuns {wide : Bool} {consts : List (String × TExpr)}
    {te : TExpr} {σ : AbiLayout} (hσ : Census.deriveAbi wide consts te = .ok σ) {sa : AState}
    {v : Value} (hrun : haxRuns σ (te : HaxModule) sa v) :
    ∀ b ∈ σ.bounds, (sa.regs b.1).toNat ≤ b.2 := by
  obtain ⟨env, fuel, env', henv, hr, hv⟩ := (haxRuns_single σ te sa v).mp hrun
  exact deriveAbi_bounds_hold hσ henv hr hv

end CatCrypt.Crypto.SecureCompilation.Haxc.DeriveBounds
