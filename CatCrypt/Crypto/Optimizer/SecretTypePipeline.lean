/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.SecretType
import CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline

/-!
# Compositional CT across the whole canonicalize pipeline (#594 capstone)

`SecretType.lean` proved the two algebraic `Com → Com` passes' secret-taint
facts in isolation:

* `peepCom_wellTainted` — the local peephole **preserves** the taint-typing
  invariant exactly (it rewrites `binE bop a b ↦ binE bop' a b`, reusing the
  same argument variables, so every binder's `exprTaint` is unchanged);
* `saturateCom_comMaxTaint_le` — the bounded equality-saturation engine only
  ever **declassifies**: it never raises the program's overall secrecy level
  `comMaxTaint` (the join of every binder's taint down the let-chain).

`Optimizer/Rewrite/ComPipeline.lean` composes the two into the canonical
algebraic-canonicalisation transform

```
comAlgebraicPipeline fuel c k = saturateCom fuel (peepCom c) k
```

This file lifts the per-pass results to that **composed** pipeline: the whole
canonicalize pass is declassify-monotone — the program's overall secrecy level
never increases through it.

## The bridge

The two per-pass lemmas live at different granularities: peephole's is an
*exact, per-binder* `WellTainted`/`exprTaint` statement, while saturate's is the
*scalar* `comMaxTaint` summary (the only transitively-composable form in the
two-point lattice — see the `SecretType.lean` §8 header). We bridge them at
`comMaxTaint`:

* `peepCom_comMaxTaint` — since `peepExpr` preserves every binder's `exprTaint`
  exactly (`peepExpr_exprTaint`), and `comMaxTaint` is the join of those binder
  taints down the chain, the peephole preserves `comMaxTaint` **exactly** (an
  equality, the `comMaxTaint` shadow of `peepCom_wellTainted`);
* compose that equality with `saturateCom_comMaxTaint_le` (and reflexivity /
  `SecretLevel.leq` rewriting) to get the pipeline bound.

The result is non-vacuous: peephole contributes a genuine equality (binder
taints are preserved, not trivially) and saturate a genuine `⊑ₛ` (it can
strictly drop a binder from `sec` to `pub`, as the `demoMulZero` validation
shows), composed by transitivity of the lattice order.

All goals closed.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.SecretType

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open CatCrypt.Crypto.Optimizer.Rewrite.Peephole
open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline

/-! ## 1. Peephole preserves the program's overall secrecy level exactly

`comMaxTaint` is the join of every binder's `exprTaint` threaded down the
let-chain. The peephole rewrites each binder to one over the *same* argument
variables (`peepExpr_exprTaint`), so every binder's `exprTaint` is unchanged and
the env threaded into the body is identical on both sides. Hence the whole join
— `comMaxTaint` — is preserved **exactly**. This is the `comMaxTaint` shadow of
the exact `peepCom_wellTainted` invariant, in the scalar form that composes with
the saturation engine's declassification bound. -/

/-- **The peephole preserves the program's overall secrecy level exactly.**
`comMaxTaint T (peepCom c) = comMaxTaint T c`. Each binder is rewritten over the
same argument variables (`peepExpr_exprTaint`), so its `exprTaint` is unchanged
and the threaded env is identical down the chain. -/
theorem peepCom_comMaxTaint {Γ : Ctxt jasminDialect} {t : JasminTy} :
    ∀ (T : Taint Γ) (c : Com jasminDialect Γ t),
      comMaxTaint T (peepCom c) = comMaxTaint T c
  | _, .ret _ => rfl
  | T, .var e body => by
      simp only [peepCom, comMaxTaint]
      rw [peepExpr_exprTaint T e]
      rw [peepCom_comMaxTaint (T.cons (exprTaint T e)) body]

/-! ## 2. The capstone: the whole canonicalize pipeline declassifies monotonically

Composing the peephole's exact `comMaxTaint`-preservation (§1) with the
saturation engine's `comMaxTaint`-non-increase (`saturateCom_comMaxTaint_le`):
the composed `comAlgebraicPipeline` (peephole then bounded saturation) never
raises the program's overall secrecy level. The compositional-CT invariant now
spans the entire algebraic-canonicalisation stage of the optimiser. -/

/-- **The whole canonicalize pipeline is declassify-monotone.**
`comMaxTaint T (comAlgebraicPipeline fuel c k) ⊑ₛ comMaxTaint T c`: the
program's overall secrecy level never increases through the composed
peephole-then-equality-saturation pass.

Proof: `comAlgebraicPipeline fuel c k = saturateCom fuel (peepCom c) k`. The
saturation engine does not raise the level of `peepCom c`
(`saturateCom_comMaxTaint_le`), and the peephole preserves the level of `c`
exactly (`peepCom_comMaxTaint`); rewriting the latter equality into the former
bound gives the result. The capstone of the #594 compositional-CT arc: peephole
*preserves* taint, the egraph engine *declassifies monotonically*, and the
composition stays within the program's taint budget. -/
theorem comAlgebraicPipeline_comMaxTaint_le {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (T : Taint Γ) (c : Com jasminDialect Γ t) (k : KEnv Γ) :
    comMaxTaint T (comAlgebraicPipeline fuel c k) ⊑ₛ comMaxTaint T c := by
  unfold comAlgebraicPipeline
  have hsat : comMaxTaint T (saturateCom fuel (peepCom c) k) ⊑ₛ comMaxTaint T (peepCom c) :=
    saturateCom_comMaxTaint_le fuel T (peepCom c) k
  rwa [peepCom_comMaxTaint T c] at hsat

/-! ## 3. Validation on the egraph demo

The `demoMulZero` program (`x * 0` via an explicit `regConst 0` binder) under a
`sec`-input assignment: the peephole half does not fire (no `sub a a` / `and a a`
idiom), and the saturation half collapses the `mul x c0` binder to `and c0 c0`,
dropping the secret `x`. So the whole pipeline strictly declassifies the
program's overall secrecy level from `sec` to `pub` — well within the
`⊑ₛ`-bound the capstone guarantees. -/

/-- The pipeline (fuel 4) strictly declassifies the demo's overall secrecy level
from `sec` to `pub` (peephole no-op, saturation drops the secret `x`). -/
example : comMaxTaint egDemoTaint (comAlgebraicPipeline 4 demoMulZero demoK) = .pub := by
  decide

/-- **The whole canonicalize pipeline never raises the demo's overall secrecy
level.** Here it strictly declassifies `sec ↦ pub`. Via
`comAlgebraicPipeline_comMaxTaint_le`. -/
example :
    comMaxTaint egDemoTaint (comAlgebraicPipeline 4 demoMulZero demoK)
      ⊑ₛ comMaxTaint egDemoTaint demoMulZero :=
  comAlgebraicPipeline_comMaxTaint_le 4 egDemoTaint demoMulZero demoK

end CatCrypt.Crypto.Optimizer.SecretType
