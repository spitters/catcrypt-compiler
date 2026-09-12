/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSimulates

/-!
# H3.tertia: leaf-call simulation cases

Handles `letBind _ (app _ _) _` and `assign _ (app _ _)` arms of
`haxToLowCT`.  The key piece is `LeafCallAgrees`, a per-leaf
agreement predicate that consumers populate when they wire a
concrete `LeafSpec`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpType IntWidth Value Env Outcome Builtins
                   denote defaultBuiltins)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT RustState RustExec LeafSpec Located
   rsSetTower rsSetScalar)

/-! ## §1  Source-side inverse for `.app` with all-var arguments

The general `.app` arm's `denote` can in principle update the env via
`denoteArgs` (each sub-expression is a `StateM` action).  But the
`haxToLowCT` translation only accepts `.app f args` when every arg is
a plain `.var` — see `haxArgsToLocated`.  Under that restriction
`denoteArgs` is env-preserving.

We capture two pieces:

* `AllVars`: a relational predicate pairing an `args : List ImpExpr`
  with a `vals : List Value` such that each `args[i]` is `.var n`
  with `env n = some vals[i]`.  This is the easiest shape for an
  inductive proof on the parallel structure of the two lists.

* `denoteArgs_vars`: under `AllVars env args vals`, `denoteArgs`
  returns `(some vals, env)`.

* `evalImp_app_vars_inv`: lifts the result to `evalImp` for `.app`,
  yielding `bi f vals = some v` and `env' = env`. -/

/-- Relational shape: `args` is a list of `.var` lookups that the
    environment `env` resolves to the parallel list `vals`. -/
inductive AllVars (env : Env) : List ImpExpr → List Value → Prop where
  | nil  : AllVars env [] []
  | cons : ∀ n v as vs, env n = some v → AllVars env as vs →
           AllVars env (.var n :: as) (v :: vs)

/-- `denoteArgs` on an `AllVars` list returns `some vals` with env
    unchanged. -/
theorem denoteArgs_vars (bi : Builtins) (fuel : Nat) (env : Env) :
    ∀ {args : List ImpExpr} {vals : List Value},
      AllVars env args vals →
      (Hax.denoteArgs bi fuel args).run env = (some vals, env)
  | [], [], _ => by
      simp [Hax.denoteArgs, StateT.run, pure, Pure.pure, StateT.pure]
  | _, _, .cons n v as vs hEnv hRest => by
      have ih := denoteArgs_vars bi fuel env hRest
      -- Unfold denoteArgs on (.var n :: as)
      simp only [Hax.denoteArgs, Hax.denote,
                 bind, Bind.bind, StateT.bind, StateT.run,
                 get, getThe, MonadStateOf.get, StateT.get,
                 pure, Pure.pure, StateT.pure, hEnv]
      -- Tail reduces by IH
      show (match (Hax.denoteArgs bi fuel as).run env with
            | (rest, env') => (Option.map (v :: ·) rest, env')) =
           (some (v :: vs), env)
      rw [ih]
      simp

/-- Build an `AllVars` witness from a `∀ a ∈ args, ∃ n w, ...`
    hypothesis.  This is the constructive bridge from "every arg is a
    var that env resolves" to a parallel `vals` list. -/
theorem allVars_of_forall (env : Env) :
    ∀ (args : List ImpExpr),
      (∀ a ∈ args, ∃ n, a = .var n ∧ ∃ w, env n = some w) →
      ∃ vals, AllVars env args vals
  | [], _ => ⟨[], AllVars.nil⟩
  | a :: as, h => by
      obtain ⟨n, ha, w, hw⟩ := h a (by simp)
      subst ha
      have hRest : ∀ a' ∈ as, ∃ n, a' = .var n ∧ ∃ w, env n = some w := by
        intro a' ha'
        exact h a' (by simp [ha'])
      obtain ⟨vs, hVs⟩ := allVars_of_forall env as hRest
      exact ⟨w :: vs, AllVars.cons n w as vs hw hVs⟩

/-- Source-side inverse for `.app f args` when all `args` are plain
    `.var` lookups (the only shape `haxToLowCT` accepts).

    Yields a parallel `vals` list (via the `AllVars` relation),
    `bi f vals = some v`, and `env' = env`. -/
theorem evalImp_app_vars_inv (bi : Builtins) (fuel : Nat) (f : String)
    (args : List ImpExpr) (env : Env) (v : Value) (env' : Env)
    (hVars : ∀ a ∈ args, ∃ n, a = .var n ∧ ∃ w, env n = some w)
    (h : evalImp bi fuel (.app f args) env = some (v, env')) :
    ∃ vals, AllVars env args vals ∧ bi f vals = some v ∧ env' = env := by
  -- Build the parallel `vals` list
  obtain ⟨vals, hAV⟩ := allVars_of_forall env args hVars
  -- denoteArgs reduces by `denoteArgs_vars`
  have hda := denoteArgs_vars bi fuel env hAV
  -- Unfold evalImp and denote on .app
  unfold evalImp at h
  simp only [denote, bind, Bind.bind, StateT.bind, StateT.run,
             pure, Pure.pure] at h
  -- Normalise StateT.run on `hda` so the rewrite finds its target.
  simp only [StateT.run] at hda
  rw [hda] at h
  -- Reduce the outer `match (some vals, env)` to expose the `bi f vals` case.
  dsimp only at h
  cases hbi : bi f vals with
  | none =>
    rw [hbi] at h
    simp [StateT.pure] at h
  | some w =>
    rw [hbi] at h
    simp only [StateT.pure, pure, Pure.pure, Option.some.injEq,
               Prod.mk.injEq] at h
    obtain ⟨hvw, henv⟩ := h
    exact ⟨vals, hAV, by rw [hbi, hvw], henv.symm⟩

/-! ## §2  Per-leaf agreement predicate `LeafCallAgrees`

Given a Builtins-side leaf `f`, a LeafSpec, a TowerType `dt` for the
destination, and a fuel bound `N`, `LeafCallAgrees` says: whenever the
Builtins side successfully calls `f` on `vals` producing `vRes`, and
`vRes` decodes to a scalar `n`, then a `RustExec` step on the
corresponding `.RCall` exists yielding a state whose scalar slot at
`dest` equals `n`.

This is the per-leaf assumption a consumer must populate when they
wire a concrete `LeafSpec`.  We keep `dest`, `args`, and `rs`
universally quantified so the predicate is one-shape-fits-all. -/

/-- Per-leaf simulation predicate.  Populated per leaf by the consumer
    who wires the concrete `LeafSpec`. -/
def LeafCallAgrees (bi : Builtins) (leafSpec : LeafSpec)
    (f : String) (dt : TowerType) (N : Nat) : Prop :=
  ∀ (rs : RustState) (dest : String) (args : List Located)
    (vals : List Value) (vRes : Value),
    bi f vals = some vRes →
    ∀ n, valueToScalar vRes = some n →
      ∃ rs', RustExec N leafSpec
              (.RCall f { locVar := dest, locSrc := dt } args) rs rs'
           ∧ rs'.rsScalar dest = n

/-! ## §3  Notes on `Goal 3`/`Goal 4` (simulation instances)

The full `haxToLowCT_simulates_letBind_app` and
`haxToLowCT_simulates_assign_app` instances require two pieces
beyond what this file lands:

1. **Agreement-extension lemma `envAgreesRust_extend_scalar`** — already
   landed in `HaxToLowCTSim_Agreement.lean` (and duplicated `private`
   in `HaxToLowCTSim_AssignMatch.lean`).  Lifts
   `envAgreesRust env rs` to `envAgreesRust (env.extend name v)
   (rsSetScalar rs name n)` given `valueToScalar v = some n`.

2. **Scalar/tower bridge.**  `RustExec.call` updates only the tower
   slot (`locatedUpdate`), not the scalar slot.  So for a leaf whose
   return value `vRes` decodes to a scalar (via `valueToScalar`), the
   only way `LeafCallAgrees` can be populated is if (a) the leafSpec
   actually maintains `rsScalar dest = n` separately (e.g. via a
   pre-call `RScalarSet` or because the post-state's scalar was
   already `n`), or (b) the value is one of the "constant decode"
   cases (`.unit → 0`, `.bool _ → {0,1}`) where the leaf's scalar
   side-effect is incidental.  In practice, scalar-returning leaves
   in CryptoSSA's u64 fragment (`u64_add`, etc.) use a parallel
   scalar oracle — that oracle is not part of the current `LeafSpec`
   structure (which only has `call`, `limbStore`, etc., all on tower
   values).

The cleanest way to close the simulation instances is to extend
`LeafSpec` with a scalar-call oracle and broaden `LeafCallAgrees`
to dispatch on whether `dt = .TU64` (scalar leaf) or otherwise
(tower leaf, where `envAgreesRust`'s scalar predicate is vacuous on
the new binding).  That refactor is out of scope for the current
file; we leave the two simulation instances open as a documented
follow-up rather than commit half-proofs with sorries.

The two essential pieces — the source-side inverse and the
per-leaf agreement predicate — are landed and verified here. -/

end CatCrypt.Crypto.Hax
