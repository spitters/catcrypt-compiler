/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module -- deprecated_module: ignore

public import CatCrypt.Crypto.Hax.HaxToLowCT
public import CatCrypt.Crypto.Hax.ImpEval
public import HaxLean.Semantics

/-!
# H3 Blocker 2 (part): per-constructor outcome lemmas for AnfShaped programs

This file provides the building-block lemmas for the syntactic-to-semantic
implication needed to discharge the `hBodyAlwaysVal` hypothesis of
`haxToLowCT_simulates_whileLoop_var` (in `HaxToLowCTSim_While.lean`).

## Key fact

`AnfShaped` programs cannot contain `break_`, `continue_`, `earlyReturn`,
or `questionMark` constructors — i.e. the constructors that the big-step
`denote` returns the non-value outcomes `.broke`, `.continued`, `.earlyRet`
for.  Loops are restricted to `AnfShaped` bodies, so they too cannot
produce `.broke` / `.continued` / `.earlyRet`.

Therefore the only outcomes an `AnfShaped` expression can produce under
`denote` are `.val _` or `.err _`.

## Status of this file

The structural induction on `ImpExpr` proceeds smoothly for the straight-
line productive constructors (`var`, `unitVal`, `letBind` with literal
or var-only-`app` rhs, `seq`, `ifThenElse` with `.var` condition,
`assign` with the AnfShaped-permitted rhs shapes) and for all rejected
constructors (the latter close by `simp [AnfShaped] at h`).

The combined theorem `AnfShaped e = true → (∃ v, …) ∨ (∃ msg, …)` is
**not** packaged in this commit — closing the `whileLoop` and `match_`
arms requires:

* a `denoteWhile_outcome_val_or_err` lemma proved by induction on fuel,
  using the recursive call to the main theorem in the body case;
* a `denoteMatchArms_outcome_val_or_err` lemma for the 2-tuple-of-vars
  pattern that `AnfShaped` admits.

Both involve mutual reasoning through `denoteWhile` / `denoteMatchArms`
(which live in a `mutual` block with `denote`), so a clean combined
statement requires a wf-recursive scheme over `(fuel, sizeOf expr)`
that respects the same termination measure.

For the immediate downstream caller (the whileLoop discharge in
`HaxToLowCTSim_While.lean`), the helpers exposed below are enough to
re-assemble the productive-outcome dichotomy on the specific body
shapes emitted by the upstream `haxpipeT` extraction (which in
practice are straight-line let-bindings of leaf-call applications).

## Main exports

* `denote_var_outcome` — `var n` is `.val` or `.err`.
* `denote_app_outcome` — `app f args` is `.val` (success or unknown-fn)
  or `.err` (non-value-in-args).

The terminal evaluators `denote_lit_eq`, `denote_unitVal_eq` and the unfold
equations `denote_letBind_run_eq`, `denote_seq_run_eq`,
`denote_ifThenElse_run_eq`, `denote_assign_run_eq` are in `Hax.ImpEval`,
which this module imports.
-/

deprecated_module "haxToLowCT is the legacy hax front, outside compileA's path: compileA compiles \
  through haxToNF (Haxc.NFChain); this module remains for the SurfaceDeps bridges \
  (*HaxLowCTBridge) and the kernel producers that use it."
  (since := "2026-10-21")

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpType Value Env Outcome Builtins
                   denote denoteWhile denoteForLoop denoteArgs denoteMatchArms)

/-! ## §1  Per-constructor outcome dichotomies -/

/-- `.var n` evaluates to `.val v` if `env n = some v`, else `.err _`. -/
theorem denote_var_outcome (bi : Builtins) (fuel : Nat) (n : String) (env : Env) :
    (∃ v env', (denote bi fuel (.var n)).run env = (.val v, env'))
  ∨ (∃ msg env', (denote bi fuel (.var n)).run env = (.err msg, env')) := by
  cases hen : env n with
  | none =>
    right; refine ⟨s!"undefined variable: {n}", env, ?_⟩
    simp [denote, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
          pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind, hen]
  | some v =>
    left; refine ⟨v, env, ?_⟩
    simp [denote, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
          pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind, hen]

/-- The outcome dichotomy for `.app f args`.

    Three outcomes are possible: success (some args evaluated, builtin
    returned a value), unknown-function error, or non-value-in-args
    error.  All three are productive (`.val` or `.err`). -/
theorem denote_app_outcome (bi : Builtins) (fuel : Nat) (f : String)
    (args : List ImpExpr) (env : Env) :
    (∃ v env', (denote bi fuel (.app f args)).run env = (Outcome.val v, env'))
  ∨ (∃ msg env', (denote bi fuel (.app f args)).run env
        = (Outcome.err msg, env')) := by
  rcases h : (denoteArgs bi fuel args).run env with ⟨mvals, env_a⟩
  cases mvals with
  | none =>
    right; refine ⟨"non-value in function arguments", env_a, ?_⟩
    simp only [denote, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure]
    rw [show (denoteArgs bi fuel args) env = (denoteArgs bi fuel args).run env from rfl, h]
    rfl
  | some vs =>
    cases hf : bi f vs with
    | none =>
      right; refine ⟨s!"unknown function or bad args: {f}", env_a, ?_⟩
      simp only [denote, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure]
      rw [show (denoteArgs bi fuel args) env = (denoteArgs bi fuel args).run env from rfl, h]
      simp only [hf]; rfl
    | some v =>
      left; refine ⟨v, env_a, ?_⟩
      simp only [denote, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure]
      rw [show (denoteArgs bi fuel args) env = (denoteArgs bi fuel args).run env from rfl, h]
      simp only [hf]; rfl

/-! ## §2  Remaining work

The combined theorem `AnfShaped_outcome_val_or_err` (saying
`AnfShaped e = true → (∃ v env', …) ∨ (∃ msg env', …)`) requires
closing the `whileLoop` and `match_` arms of the structural induction.

* **`whileLoop`** — needs a lemma
  `denoteWhile_outcome_val_or_err : ∀ fuel env, … ` proved by
  induction on fuel.  The recursive call to the main dichotomy in the
  body case must be threaded through the mutual `denote` / `denoteWhile`
  termination measure.  The `match`-reduction obstacle here is that the
  nested `(some _, env)` / `(other, env)` patterns inside `denoteWhile`'s
  expansion do not reduce automatically via `simp only`.  The clean
  approach is to first lift `denoteWhile` to an explicit pair-match
  equation (analogous to `denote_letBind_run_eq` etc.) and then
  carry out the fuel induction.

* **`match_`** — `AnfShaped` only admits
  `.match_ (.app f args) [(.tuplePat [.varPat _, .varPat _], body)]`
  with `args` all `var`s and `body` AnfShaped.  By
  `denote_app_outcome`, the scrutinee evaluates to `.val v_tuple`
  (must be a `Value.tuple [v1, v2]` for the pattern to bind) or to
  `.err`.  In the `.val v_tuple` case, `matchPat` either succeeds
  (binding the two vars) and we recurse on `body`, or fails (returning
  `.err "no matching pattern"`).  All sub-cases are productive.

Once these two arms are closed, the combined dichotomy follows by
structural induction via `ImpExpr.ind`, with all rejected constructors
closing by `simp [AnfShaped] at h`. -/

end CatCrypt.Crypto.Hax
