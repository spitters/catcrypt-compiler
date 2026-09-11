/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.TranslationValidation

/-!
# Translation validation against the algebraic canonicalisation pipeline (#591)

A second arm of the verified translation-validation (TV) checker for the typed
VIR `jasminDialect`. The base checker `TranslationValidation.tvCheck` accepts a
candidate `c'` when it is structurally the input or the verified local peephole
output. This file widens the *accepted transform* to the **full algebraic
canonicalisation pipeline** `comAlgebraicPipeline` (peephole, then bounded
equality-saturation under a known-constant environment; see
`Rewrite/ComPipeline.lean:75`).

The complementary #591 *scheduler* variant lives in
`TranslationValidationSched.lean`: there the accepted transform is the LowCT
instruction schedule. Here it is the `Com`-level algebraic canonicalise.

## What is checked

`tvCheckCanon fuel k c c'` returns `true` exactly when the candidate `c'` is
structurally equal (via the verified `comEqB`) to the canonicalisation
`comAlgebraicPipeline fuel c k` that the in-tree *proved* pipeline would produce.
The optimizer/search engine that proposes `c'` is never trusted: only this
Boolean check, plus the pipeline's own denotation-preservation theorem, is in
the TCB.

## What is proved

* `tvCheckCanon_sound` — `tvCheckCanon fuel k c c' = true → ∀ V,
  KEnv.Consistent k V → c'.denote V = c.denote V`. Composes the verified
  `comEqB_sound` (the candidate denotes the same as the canonical form) with
  `comAlgebraicPipeline_denote` (the canonical form denotes the same as the
  input, under any known-constant environment consistent with the valuation).

The `KEnv.Consistent k V` hypothesis is threaded exactly as
`comAlgebraicPipeline_denote` requires: the known-constant environment that
drives equality-saturation must agree with the valuation at which we evaluate.
Sound and incomplete, like the base checker, and with no enlargement of the TCB
beyond the already-proved pipeline.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.TranslationValidation

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open CatCrypt.Crypto.Optimizer.Rewrite.Peephole
open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline

/-! ## The algebraic-canonicalisation TV checker -/

/-- **The verified algebraic-canonicalisation TV checker.** Accepts the
candidate `c'` (output of an untrusted optimizer oracle) against the input `c`
when `c'` is structurally the result of the proved algebraic canonicalisation
pipeline `comAlgebraicPipeline fuel c k` (peephole then `fuel`-bounded equality
saturation under the known-constant environment `k`). Decidable, hence
executable as a checker; reuses the verified `comEqB`. -/
def tvCheckCanon {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (k : KEnv Γ) (c c' : Com jasminDialect Γ t) : Bool :=
  comEqB c' (comAlgebraicPipeline fuel c k)

/-- **Soundness of the algebraic-canonicalisation TV checker (#591).** If
`tvCheckCanon fuel k c c' = true`, then for every valuation `V` for which the
known-constant environment `k` is consistent, the candidate `c'` denotes the
same function as the input `c`. The optimizer that produced `c'` is *not*
trusted: this composes the verified `comEqB_sound` with the proved pipeline
preservation `comAlgebraicPipeline_denote`. Incomplete (only candidates equal to
the canonical form are accepted) but never unsound. -/
theorem tvCheckCanon_sound {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (k : KEnv Γ) (c c' : Com jasminDialect Γ t)
    (h : tvCheckCanon fuel k c c' = true) :
    ∀ V : Ctxt.Valuation Γ, KEnv.Consistent k V → c'.denote V = c.denote V := by
  intro V hk
  unfold tvCheckCanon at h
  rw [← comEqB_sound c' (comAlgebraicPipeline fuel c k) h V,
      comAlgebraicPipeline_denote fuel c k V hk]

/-! ## Self-contained validation

Reusing `Egraph.demoMulZero` (`x ↦ x * 0`) with the demo known-constant
environment `demoK`: the canonical form `comAlgebraicPipeline 4 demoMulZero
demoK` is by definition accepted, and `tvCheckCanon_sound` certifies that it
denotes the same function as the input. -/

/-- **Accept (canonicalisation arm).** The candidate equal to the algebraic
canonicalisation of the demo is certified by the checker. -/
example :
    tvCheckCanon 4 demoK demoMulZero (comAlgebraicPipeline 4 demoMulZero demoK)
      = true := by
  decide

/-- The accepted canonical candidate genuinely denotes the same function as the
input (both map `x` to `0`) — the soundness theorem applied to the demo. -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (comAlgebraicPipeline 4 demoMulZero demoK).denote V = demoMulZero.denote V :=
  tvCheckCanon_sound 4 demoK demoMulZero _ (by decide) V (demoK_consistent V)

/-- Smoke check: the module builds and its obligations close. -/
theorem tvCanon_compiles : True := trivial

end CatCrypt.Crypto.Optimizer.TranslationValidation
