/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JForProgUnroll
public import CatCrypt.Crypto.SecureCompilation.VIR.JForProgUnroll

/-!
# Denotation-preserving loop-invariant code motion (LICM) — the hoist transform

The bounded-loop layer (`JasminPrint.JForProg`, `JForProgCT`, `JForProgUnroll`)
gives a loop `for i in 0..n { acc := step acc }` the denotation

  `JForProg.denote p init = (List.range p.n).foldl (fun acc _ => p.step acc) init`.

`LoopInvariantHoist.lean` provides the *analysis-as-labelling* form of LICM:
it flags which body binders are loop-invariant, and its `Com → Com` rewrite is
the identity (the labelling is consumed downstream). This file is the
complementary, **structurally real** transform: it actually *moves* a
loop-invariant subcomputation out of the loop body to a once-per-call prelude,
and proves the moved program denotes the *same total function* as the original.

## What "loop-invariant" means here, and why hoisting is sound

We model a loop body whose per-iteration step factors through an explicit
subcomputation:

  `step acc = body (pre acc) acc`

where

* `pre : ⟦accTy⟧ → ⟦invTy⟧` is the candidate subexpression to hoist, and
* `body : ⟦invTy⟧ → ⟦accTy⟧ → ⟦accTy⟧` is the rest of the iteration, which
  consumes the precomputed value.

The subexpression `pre` is **loop-invariant** exactly when its value does not
change across iterations — i.e. it does not read the loop-carried accumulator.
Formally this is the hypothesis

  `hInv : ∀ a b, pre a = pre b`        (`Invariant pre`)

(`pre` is a constant function of the accumulator). This is the denotational
shadow of the syntactic criterion in `LoopInvariantHoist.analyzeLicm`: a binder
whose argument variables never resolve to `acc` computes the same value every
iteration, so its denotation is constant in `acc`.

Under that hypothesis the hoisted loop

  `hoistedStep c acc = body c acc`        with        `c := pre init`

computes the same step *every* iteration as the original — because the original
recomputes `pre acc`, but `pre acc = pre init` by invariance — so the two folds
agree pointwise and therefore agree on the whole `range n` iteration. That is
`licm_denote`.

This is a *sound transform* that is not the identity: `licm` produces a new
`JForProg` whose body is `body c · ` (the hoisted-out `pre` is gone from the
per-iteration work; it is evaluated once into `c`). The denotation theorem
reuses the `JForProgUnroll` fold-congruence reasoning (`List.range`/`foldl`),
exactly the existing bounded-loop denotation machinery.

## Scope (conservative seed)

* We hoist **one** loop-invariant subcomputation `pre`, given the factorisation
  `step = fun acc => body (pre acc) acc`. This is the simplest sound case — a
  single leading loop-invariant value lifted to the prelude — and it is a
  proven seed, not a stub: `licm_denote` is a real equality of denotations
  under the invariance hypothesis.
* Soundness rests *only* on `Invariant pre`. We do not assume anything about
  `body`; in particular `body` may still read `acc` freely (that is the
  loop-carried part that must stay inside the loop).
* The transform lives at the `JForProg` step/denotation layer, where the loop's
  total semantics is the `foldl`. Wiring the factorisation back to a concrete
  `Com` body (splitting the let-chain so the `pre` binders land in a prelude
  `Com` via De Bruijn renumbering) is the documented next step; the
  `LoopInvariantHoist.analyzeLicm` analysis already identifies *which* binders
  form `pre`. The denotation-preservation content — the part a verified
  optimiser must discharge — is proved here.

No `sorry`, no `native_decide`, no new axioms: `licm_denote` closes by induction
over `List.range n` (the same fold-congruence skeleton as
`JForProgUnroll.foldl_step_congr`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.LoopInvariantMotion

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint

/-! ## 1. The loop-invariance predicate -/

/-- **A subcomputation is loop-invariant** when its value is independent of the
    loop-carried accumulator: `pre` returns the same result for every
    accumulator value. This is the denotational shadow of the syntactic
    criterion in `LoopInvariantHoist.analyzeLicm` — a binder whose argument
    variables never resolve to `acc` has a denotation that is constant in
    `acc`. -/
def Invariant {accTy invTy : JasminTy} (pre : ⟦accTy⟧ → ⟦invTy⟧) : Prop :=
  ∀ a b : ⟦accTy⟧, pre a = pre b

/-- A constant subcomputation (one literally ignoring its argument) is
    loop-invariant. The canonical LICM target — a round constant / twiddle
    factor materialised every iteration. -/
theorem Invariant.const {accTy invTy : JasminTy} (c : ⟦invTy⟧) :
    Invariant (accTy := accTy) (fun _ => c) := fun _ _ => rfl

/-! ## 2. The hoisted step and the `licm` transform

A loop whose `step` factors as `step acc = body (pre acc) acc` with a
loop-invariant `pre` can hoist `pre` to a prelude: precompute `c := pre init`
once, then run `hoistedStep c acc = body c acc` every iteration. -/

/-- The per-iteration step *after* hoisting: the invariant value `c` is supplied
    from the prelude, so the loop body only does the accumulator-dependent
    `body`. -/
def hoistedStep {accTy invTy : JasminTy}
    (body : ⟦invTy⟧ → ⟦accTy⟧ → ⟦accTy⟧) (c : ⟦invTy⟧)
    (acc : ⟦accTy⟧) : ⟦accTy⟧ :=
  body c acc

/-- **The LICM transform on the loop-step semantics.** Given a body factored as
    `step acc = body (pre acc) acc` and the initial accumulator `init`, produce
    the hoisted total loop: precompute `c := pre init` once, then iterate
    `hoistedStep body c` over `range n`.

    The hoisted-out subcomputation `pre` is evaluated exactly once (into `c`)
    instead of `n` times. -/
def licm {accTy invTy : JasminTy} (n : Nat)
    (body : ⟦invTy⟧ → ⟦accTy⟧ → ⟦accTy⟧) (pre : ⟦accTy⟧ → ⟦invTy⟧)
    (init : ⟦accTy⟧) : ⟦accTy⟧ :=
  let c := pre init
  (List.range n).foldl (fun acc _ => hoistedStep body c acc) init

/-! ## 3. Denotation preservation -/

/-- A `foldl`-congruence over `List.range n`: two index-ignoring step functions
    that agree pointwise produce the same fold from any seed. (Same shape as
    `JForProgUnroll.foldl_step_congr`; re-stated locally to keep this file's
    dependency surface minimal.) -/
theorem foldl_range_congr {accTy : JasminTy}
    {f g : ⟦accTy⟧ → ⟦accTy⟧} (hfg : ∀ acc, f acc = g acc) (n : Nat) :
    ∀ init : ⟦accTy⟧,
      (List.range n).foldl (fun acc _ => f acc) init
        = (List.range n).foldl (fun acc _ => g acc) init := by
  induction n with
  | zero => intro init; rfl
  | succ n ih =>
      intro init
      rw [List.range_succ, List.foldl_append, List.foldl_append, ih init]
      simp [hfg]

/-- **LICM is denotation-preserving (the hoist is sound).**

    For any loop count `n`, any body factorisation `step acc = body (pre acc) acc`,
    and any initial accumulator `init`, *if* `pre` is loop-invariant
    (`Invariant pre`), then hoisting `pre` out of the loop computes the same
    total result as the original loop:

      `licm n body pre init`
        `= (List.range n).foldl (fun acc _ => body (pre acc) acc) init`.

    The right-hand side is exactly the original loop's denotation
    (`JForProg.denote` with `step acc = body (pre acc) acc`), so the hoisted
    program denotes the same function.

    Proof: the hoisted step uses the constant `c = pre init`, while the original
    recomputes `pre acc` each iteration. By invariance `pre acc = pre init = c`,
    so the two step functions agree pointwise; `foldl_range_congr` lifts that to
    the whole `range n` fold. -/
theorem licm_denote {accTy invTy : JasminTy} (n : Nat)
    (body : ⟦invTy⟧ → ⟦accTy⟧ → ⟦accTy⟧) (pre : ⟦accTy⟧ → ⟦invTy⟧)
    (hInv : Invariant pre) (init : ⟦accTy⟧) :
    licm n body pre init
      = (List.range n).foldl (fun acc _ => body (pre acc) acc) init := by
  unfold licm hoistedStep
  -- Goal: fold of `body (pre init) ·` = fold of `body (pre ·) ·`.
  -- Pointwise the two steps agree because `pre init = pre acc` by invariance.
  refine foldl_range_congr (f := fun acc => body (pre init) acc)
            (g := fun acc => body (pre acc) acc) ?_ n init
  intro acc
  rw [hInv init acc]

/-! ## 4. Phrased against `JForProg.denote`

`licm_denote`'s right-hand side is literally `JForProg.denote` for a `JForProg`
whose `step` is the factored body. We package that so the result reads as a
denotation equality between the original loop and its hoisted form. -/

/-- **LICM preserves `JForProg.denote`.** Let `p : JForProg accTy` be a bounded
    loop whose per-iteration step factors as `p.step acc = body (pre acc) acc`
    through a loop-invariant subcomputation `pre`. Then the hoisted loop
    (`licm`, which evaluates `pre` once in the prelude) denotes the same total
    function as `p`.

    This is the user-facing form: it equates `licm` directly with
    `JForProg.denote p`, exhibiting LICM as a denotation-preserving bounded-loop
    optimisation in the same family as `JForProgUnroll.UnrolledBy.denote_eq`. -/
theorem licm_denote_JForProg {accTy invTy : JasminTy} (p : JForProg accTy)
    (body : ⟦invTy⟧ → ⟦accTy⟧ → ⟦accTy⟧) (pre : ⟦accTy⟧ → ⟦invTy⟧)
    (hStep : ∀ acc, p.step acc = body (pre acc) acc)
    (hInv : Invariant pre) (init : ⟦accTy⟧) :
    licm p.n body pre init = p.denote init := by
  rw [licm_denote p.n body pre hInv init]
  unfold JForProg.denote
  exact (foldl_range_congr (f := fun acc => body (pre acc) acc)
            (g := p.step) (fun acc => (hStep acc).symm) p.n init)

/-! ## 5. Sanity checks -/

/-- On the zero-iteration loop the hoisted form is the identity on the initial
    accumulator — `pre` is never even needed (and indeed never evaluated in the
    fold). -/
example {accTy invTy : JasminTy} (body : ⟦invTy⟧ → ⟦accTy⟧ → ⟦accTy⟧)
    (pre : ⟦accTy⟧ → ⟦invTy⟧) (init : ⟦accTy⟧) :
    licm 0 body pre init = init := rfl

/-- The canonical hoist: a body that only ever reads a *constant* subexpression
    `c` (independent of `acc`) is hoist-sound for free — `Invariant.const`
    discharges the side condition, and the hoisted loop matches the original. -/
example {accTy invTy : JasminTy} (n : Nat)
    (body : ⟦invTy⟧ → ⟦accTy⟧ → ⟦accTy⟧) (c : ⟦invTy⟧) (init : ⟦accTy⟧) :
    licm n body (fun _ => c) init
      = (List.range n).foldl (fun acc _ => body c acc) init := by
  rw [licm_denote n body (fun _ => c) (Invariant.const c) init]

end CatCrypt.Crypto.Optimizer.LoopInvariantMotion
