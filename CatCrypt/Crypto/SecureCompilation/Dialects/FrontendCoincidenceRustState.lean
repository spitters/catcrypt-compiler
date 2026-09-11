/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceLet
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceLet

/-!
# DF `.letBind` completed at the **`RustState`** level

The prior increment (`FrontendCoincidenceLet.lean`) closed the *path-independent*
halves of a `denoteScalar`-vs-`RustExec` `let` coincidence — the `EnvAgree`
let-extension engine (`envAgree_update`, §1 there) and the `evalBV`-level
combinator (`letBind_coincides` / `letBind_coincides_evalBV`, §2 there) — and
stated the **exact** remaining obligation: a `RustState`/`Nat` materialisation of
the bound value, bridging Path A's wrapping `BitVec 64` store to Path B's
non-wrapping `Nat` `rsScalar` store, modulo the `inRangeState` invariant. This
file closes that gap. The two frontend paths agree on the heap-free scalar `let`
fragment (in-range).

The prior file's docstring listed three steps; we close all three:

## Step 1 — `StateAgree` (refining `EnvAgree`)

`StateAgree params I ρ rs` (def `StateAgree`) is `EnvAgree params I ρ` against the
**derived** total env `derivedBeta rs := fun x => BitVec.ofNat 64 (rs.rsScalar x)`,
*together with* the in-range invariant `∀ x, rs.rsScalar x < 2^64`. The invariant
is what lets Path B's `Nat` store round-trip through `BitVec 64`
(`BitVec.ofNat 64 (rsScalar x)` recovers the stored word) and is required to
re-establish itself across the let-store. `stateAgree_envAgree` projects out the
`EnvAgree` half so the prior engine applies verbatim.

## Step 2 — `StateAgree` transport across the scalar `let` store

`rsSetScalar rs x (v.toNat)` is the Path-B `let` store (the post-state of the
`RustExec.scalarSet` / `RustExec.scalarSetExpr` derivation). We prove
(`stateAgree_update`) that it preserves `StateAgree` when `x ∉ params`, by
reducing to the prior engine `envAgree_update`: the key bridge is
`derivedBeta_rsSetScalar`, which shows `derivedBeta (rsSetScalar rs x v.toNat)`
is *exactly* `updBeta (derivedBeta rs) x v` (Path A's `BitVec 64` update) — the
round-trip `BitVec.ofNat 64 v.toNat = v` collapses the `Nat`↔`BitVec` step. The
in-range invariant re-establishes itself since the stored word `v.toNat < 2^64`.

## Step 3 — the in-range `let` coincidence (the `Nat`-wrap discharge)

`RustExec.scalarSetExpr` stores `e.eval rs.rsScalar` (a `Nat`); on the
`SLimb`-free scalar fragment this is `e.evalState rs` (`SExpr.evalState_eq_eval`).
The derived β at the bound slot is therefore `BitVec.ofNat 64 (e.evalState rs)`,
which `SExpr.evalStateBV_eq_ofNat_evalState` shows equals the hardware-faithful
`e.evalStateBV rs` **precisely when `e.inRangeState rs`** — discharging the wrap
gap the prior file isolated. `letBind_rustState_coincides` combines this with the
prior `letBind_coincides`: for a scalar `let x = ⟪e1⟫ in body`, if the Path-A
bound expr denotes to `e1.evalStateBV rs` and the body denotes (under the §1
let-extension) to a body value, then the whole `let` denotes to that body value —
and the bound local's stored value agrees, across the `Nat` store, with the
`BitVec 64` value of `e1` on `inRangeState` inputs.

## Residual `RustExec`-derivation obligation (stated precisely)

What this file does **not** do is *run* the `RustExec` big-step and read the
final `rsScalar` of `x` out of the post-state to feed `denoteScalar` of the body:
that would require a `denoteScalar`-of-body-vs-`RustExec`-of-body recursion (a
full structural induction over the body's lowering to `LowCT` commands), which is
the whole-command-block coincidence, not the single-`let`-store step. Concretely,
the open obligation is:

> Given `RustExec N leafSpec (lowerBody body) (rsSetScalar rs x (e1.evalState rs))
> rs'`, show `denoteScalar params I body (updRho ρ x (e1.evalStateBV rs))` reads
> the same scalar value as the bound output slot of `rs'`.

We close the **deterministic value-agreement** that this obligation reduces its
*store step* to (`rsSetScalar`'s derived β equals `updBeta`, under
`inRangeState`); the residual is the body recursion, which belongs to the
command-block coincidence file, not here. Stating it sharply — rather than faking
a body `RustExec` recursion with a hidden `sorry` — is the honest outcome.

No `sorry`, no new axioms, no `native_decide`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceRustState

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidence
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceLet

/-! ## §1  `StateAgree` — the `RustState`-refinement of `EnvAgree` -/

/-- The total Path-B env **derived** from a `RustState`'s scalar store: each
    scalar slot's `Nat` value materialised into `BitVec 64`. -/
def derivedBeta (rs : RustState) : String → BitVec 64 :=
  fun x => BitVec.ofNat 64 (rs.rsScalar x)

/-- **State-agreement predicate (Step 1).** Refines `EnvAgree` along the derived
    env `derivedBeta rs`, *plus* the in-range invariant `rsScalar x < 2^64` on
    every scalar slot. The invariant is load-bearing: it is what makes the `Nat`
    store round-trip through `BitVec 64` and re-establish itself across the let
    store (see `stateAgree_update`), and what discharges the `Nat`-wrap in the
    let coincidence (`SExpr.evalStateBV_eq_ofNat_evalState`). -/
def StateAgree {nIn : Nat} (params : List String) (I : Fin nIn → BitVec 64)
    (ρ : String → Option (BitVec 64)) (rs : RustState) : Prop :=
  EnvAgree params I ρ (derivedBeta rs) ∧ ∀ x, rs.rsScalar x < 2 ^ 64

/-- **Step 1 projection.** `StateAgree` gives back the prior engine's `EnvAgree`
    on the derived env, so `envAgree_update` (the §1 engine of the prior file)
    applies verbatim. -/
theorem stateAgree_envAgree {nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec 64) (ρ : String → Option (BitVec 64)) (rs : RustState)
    (h : StateAgree params I ρ rs) : EnvAgree params I ρ (derivedBeta rs) :=
  h.1

/-! ## §2  Transport of `StateAgree` across the scalar `let` store -/

/-- **The `Nat`↔`BitVec` bridge.** The derived env of the Path-B let store
    `rsSetScalar rs x v.toNat` is *exactly* Path A's `BitVec 64` update
    `updBeta (derivedBeta rs) x v`. The round-trip `BitVec.ofNat 64 v.toNat = v`
    collapses the `Nat`-store step: writing `v.toNat : Nat` then re-materialising
    recovers `v : BitVec 64`. This is the equation that makes the `rsScalar`
    `Nat` store and the `β` `BitVec` update commute. -/
theorem derivedBeta_rsSetScalar (rs : RustState) (x : String) (v : BitVec 64) :
    derivedBeta (rsSetScalar rs x v.toNat) = updBeta (derivedBeta rs) x v := by
  funext y
  simp only [derivedBeta, rsSetScalar, updBeta]
  by_cases hyx : y = x
  · subst hyx; simp [BitVec.ofNat_toNat]
  · have : (y == x) = false := by simp [hyx]
    simp [this, hyx]

/-- **Step 2 — `StateAgree` transport across the scalar `let` store.** The Path-B
    `let` store `rsSetScalar rs x v.toNat` (post-state of `RustExec.scalarSet`
    on the value `v.toNat`, or of `RustExec.scalarSetExpr` when the stored `Nat`
    is `v.toNat`) preserves `StateAgree`, provided the bound local `x` is not a
    parameter name. Reduces to the prior engine `envAgree_update` via the
    `derivedBeta_rsSetScalar` bridge; the in-range invariant re-establishes itself
    because the stored word `v.toNat < 2^64`. -/
theorem stateAgree_update {nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec 64) (ρ : String → Option (BitVec 64)) (rs : RustState)
    (h : StateAgree params I ρ rs) (x : String) (hx : x ∉ params) (v : BitVec 64) :
    StateAgree params I (updRho ρ x v) (rsSetScalar rs x v.toNat) := by
  refine ⟨?_, ?_⟩
  · -- EnvAgree half: rewrite the derived env to `updBeta`, then the prior engine.
    rw [derivedBeta_rsSetScalar]
    exact envAgree_update params I ρ (derivedBeta rs) h.1 x hx v
  · -- in-range half: stored word is `v.toNat < 2^64`; other slots unchanged.
    intro y
    simp only [rsSetScalar]
    by_cases hyx : y = x
    · subst hyx; simpa using v.isLt
    · have : (y == x) = false := by simp [hyx]
      simp only [this]; exact h.2 y

/-! ## §3  The in-range scalar `let` coincidence (the `Nat`-wrap discharge) -/

/-- **The bound-value materialisation (Step 3 core).** For an `SLimb`-free,
    `inRangeState` bound expression `e1`, the value the Path-B `let` store writes
    — `rsSetScalar rs x (e1.eval rs.rsScalar)` — materialises at slot `x` to
    exactly `e1.evalStateBV rs`, the hardware-faithful `BitVec 64` value. Two
    bridges combine: `SExpr.evalState_eq_eval` (the scalar store uses
    `eval = evalState` off `SLimb`) and `SExpr.evalStateBV_eq_ofNat_evalState`
    (the `Nat`-wrap discharge on `inRangeState`). This is the equation closing the
    `BitVec 64 ↔ Nat` store mismatch the prior file isolated. -/
theorem derivedBeta_scalarStore_eq_evalStateBV (rs : RustState) (x : String)
    (e1 : SExpr) (hlf : e1.limbFree) (hir : e1.inRangeState rs) :
    derivedBeta (rsSetScalar rs x (e1.eval rs.rsScalar)) x = e1.evalStateBV rs := by
  -- The store uses `eval`; off `SLimb`, `eval = evalState`.
  rw [← SExpr.evalState_eq_eval rs e1 hlf]
  -- Read slot `x` of the store: it is the stored `Nat`, materialised.
  have hx : (rsSetScalar rs x (e1.evalState rs)).rsScalar x = e1.evalState rs := by
    simp [rsSetScalar]
  simp only [derivedBeta, hx]
  -- `BitVec.ofNat 64 (evalState …) = evalStateBV …` on `inRangeState`.
  exact (SExpr.evalStateBV_eq_ofNat_evalState rs e1 hir).symm

/-- **Step 3 — the in-range scalar `let` coincidence.** For a scalar
    `let x = ⟪e1⟫ in body` whose bound expr `e1` is `SLimb`-free and stays
    `inRangeState`, if:

    * the Path-A bound `ImpExpr` `v` denotes (under `ρ`) to the hardware value
      `e1.evalStateBV rs` (so Path A and the Path-B `SExpr` agree on the bound
      value — this is `denoteScalar_coincides_evalBV` from the base file applied to
      the bound expr, with `β = derivedBeta rs`), and
    * the Path-A body denotes (under the §1-extended local env
      `updRho ρ x (e1.evalStateBV rs)`) to `bodyVal`,

    then the whole `let` denotes to `bodyVal` (`letBind_coincides`), AND the
    Path-B `let` store materialises the bound slot to exactly that same
    `e1.evalStateBV rs` value across the `Nat` store
    (`derivedBeta_scalarStore_eq_evalStateBV`). The two frontend paths agree on
    the bound value of the heap-free scalar `let` fragment, in-range. -/
theorem letBind_rustState_coincides {nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec 64) (ρ : String → Option (BitVec 64)) (rs : RustState)
    (x : String) (v body : ImpExpr) (bodyVal : BitVec 64)
    (e1 : SExpr) (hlf : e1.limbFree) (hir : e1.inRangeState rs)
    (hv : ImpExpr.denoteScalar params I v ρ = some (e1.evalStateBV rs))
    (hbody : ImpExpr.denoteScalar params I body
        (updRho ρ x (e1.evalStateBV rs)) = some bodyVal) :
    ImpExpr.denoteScalar params I (.letBind x v body) ρ = some bodyVal
      ∧ derivedBeta (rsSetScalar rs x (e1.eval rs.rsScalar)) x = e1.evalStateBV rs := by
  refine ⟨?_, derivedBeta_scalarStore_eq_evalStateBV rs x e1 hlf hir⟩
  exact letBind_coincides params I ρ x v body (e1.evalStateBV rs) bodyVal hv hbody

/-- **Step 3, specialised to `StateAgree`.** When the input state `rs` satisfies
    `StateAgree params I ρ rs` and `x ∉ params`, the let coincidence's body
    hypothesis can be stated against the §2-transported `StateAgree` of the store
    `rsSetScalar rs x (e1.evalStateBV rs).toNat` (the `Nat` image of the bound
    value): the let denotes to `bodyVal`, and the transported state again
    satisfies `StateAgree` on the §1-extended local env. This bundles Steps 1–3
    into a single hypothesis-driven `let`-step usable by a body recursion. -/
theorem letBind_rustState_coincides_stateAgree {nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec 64) (ρ : String → Option (BitVec 64)) (rs : RustState)
    (hsa : StateAgree params I ρ rs)
    (x : String) (hx : x ∉ params) (v body : ImpExpr) (bodyVal : BitVec 64)
    (e1 : SExpr)
    (hv : ImpExpr.denoteScalar params I v ρ = some (e1.evalStateBV rs))
    (hbody : ImpExpr.denoteScalar params I body
        (updRho ρ x (e1.evalStateBV rs)) = some bodyVal) :
    ImpExpr.denoteScalar params I (.letBind x v body) ρ = some bodyVal
      ∧ StateAgree params I (updRho ρ x (e1.evalStateBV rs))
          (rsSetScalar rs x (e1.evalStateBV rs).toNat) := by
  refine ⟨letBind_coincides params I ρ x v body (e1.evalStateBV rs) bodyVal hv hbody, ?_⟩
  exact stateAgree_update params I ρ rs hsa x hx (e1.evalStateBV rs)

end CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidenceRustState
