/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Optimizer.Rewrite.Peephole

/-!
# `Com jasminDialect` rewrite pipeline: peephole then equality-saturation (#274)

The two verified algebraic `Com → Com` passes over the typed VIR
`jasminDialect` —

* the bounded equality-saturation engine `Egraph.saturateCom` (algebraic
  identity/annihilator collapses under a known-constant environment), and
* the local syntactic peephole `Peephole.peepCom` (`sub a a ↦ xor a a`
  zeroing idiom, `and a a ↦ or a a` idempotent canonicalisation) —

are composed here into the canonical `Com`-level optimisation sequence.

## Ordering

The pipeline runs **peephole first, then equality-saturation**:

1. `peepCom` canonicalises the local two-address / zeroing idioms (it is
   purely syntactic — no constant analysis), exposing more `or a a` /
   `and a a` idempotent shapes;
2. `saturateCom` then fires the algebraic identity/annihilator rules
   (`x + 0 ↦ x`, `x * 0 ↦ 0`, `x * 1 ↦ x`, …) under the known-constant
   environment, to a fuel-bounded fixed point.

This is the *algebraic-canonicalisation* stage of the dual-IR optimiser.
The complementary *instruction-scheduling* stage runs one IR down, on the
`LowCT` block representation (`Optimizer.Pipeline.scheduleThenPipeline`,
which wires in the #273 ILP list scheduler): the VIR `Com jasminDialect`
is canonicalised here, and the lowered `LowCT` block is scheduled there.

## What is proved

* `comAlgebraicPipeline_denote` — end-to-end denotation preservation of
  the composed (peephole then saturate) `Com → Com` transform, under a
  known-constant environment consistent with the valuation.  Chains
  `Peephole.peepCom_denote` with `Egraph.saturateCom_denote`.  **Not**
  `rfl` — the peephole and the saturation engine genuinely rewrite the
  `Com` term.
* `comAlgebraicPipeline_ctSafe` — end-to-end constant-time preservation.
  `jasminDialect` is branch-free, so the composed transform produces only
  straight-line ops; `ctSafeComJ` is preserved.
* `comAlgebraicPipeline_cost_le` — the composed transform is
  cost-non-increasing (the "extraction is no worse than the input" half of
  the equality-saturation contract, composed with the peephole's own
  cost-non-increase).

All goals closed. Axiom set: `propext`, `Quot.sound` (inherited from the
two passes' preservation theorems).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open CatCrypt.Crypto.Optimizer.Rewrite.Peephole

/-! ## §1  The composed algebraic-canonicalisation transform

Peephole first (syntactic local cleanups), then the fuel-bounded
equality-saturation engine (algebraic identity/annihilator collapses). -/

/-- The composed `Com → Com` algebraic-canonicalisation transform:
    peephole, then `fuel`-bounded equality saturation under the
    known-constant environment `k`. -/
def comAlgebraicPipeline {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ) :
    Com jasminDialect Γ t :=
  saturateCom fuel (peepCom c) k

/-! ## §2  End-to-end denotation preservation -/

/-- **Composed denotation preservation.**  Running the peephole then the
    equality-saturation engine preserves the denotation of the `Com`, for
    any known-constant environment `k` consistent with the valuation `V`.
    Chains `peepCom_denote` with `saturateCom_denote`.  This is exactly
    `Peephole.peep_then_saturate_denote`, re-exported as the headline
    pipeline theorem. -/
theorem comAlgebraicPipeline_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ)
    (V : Ctxt.Valuation Γ) (hk : KEnv.Consistent k V) :
    (comAlgebraicPipeline fuel c k).denote V = c.denote V := by
  unfold comAlgebraicPipeline
  rw [saturateCom_denote fuel (peepCom c) k V hk, peepCom_denote c V]

/-! ## §3  End-to-end constant-time preservation -/

/-- **Composed CT preservation.**  `jasminDialect` is branch-free, so both
    passes produce only straight-line ops; the composed transform
    preserves the structural CT predicate `ctSafeComJ`.  This is exactly
    `Peephole.peep_then_saturate_ctSafe`, re-exported as the headline
    pipeline theorem. -/
theorem comAlgebraicPipeline_ctSafe {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ) :
    ctSafeComJ (comAlgebraicPipeline fuel c k) = ctSafeComJ c := by
  unfold comAlgebraicPipeline
  rw [saturateCom_ctSafe fuel (peepCom c) k, peepCom_ctSafe c]

/-! ## §4  Cost non-increase -/

/-- **The composed transform is cost-non-increasing.**  The peephole is
    cost-non-increasing (`peepCom_cost_le`) and so is the saturation engine
    (`saturate_cost_le`); transitivity gives the composed bound. -/
theorem comAlgebraicPipeline_cost_le {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (c : Com jasminDialect Γ t) (k : KEnv Γ) :
    comCost (comAlgebraicPipeline fuel c k) ≤ comCost c := by
  unfold comAlgebraicPipeline
  exact Nat.le_trans (saturate_cost_le fuel (peepCom c) k) (peepCom_cost_le c)

/-! ## §5  Self-contained validation

`Egraph.demoMulZero` is `x ↦ x * 0` via an explicit `regConst 0` binder.
The composed pipeline (peephole then saturation) preserves its denotation
(both map `x` to `0`) and is cost-non-increasing.  The peephole half does
not fire on this kernel (no `sub a a` / `and a a`), and the saturation
half collapses the `mul`-by-zero to `b &&& b`; the composition therefore
realises the same denotation-preserving rewrite as the saturation engine
alone, now through the canonical two-pass entry point. -/

/-- The composed pipeline (fuel 4) preserves the demo's denotation. -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (comAlgebraicPipeline 4 demoMulZero demoK).denote V = demoMulZero.denote V :=
  comAlgebraicPipeline_denote 4 demoMulZero demoK V (demoK_consistent V)

/-- The composed pipeline preserves CT on the demo. -/
example : ctSafeComJ (comAlgebraicPipeline 4 demoMulZero demoK)
        = ctSafeComJ demoMulZero :=
  comAlgebraicPipeline_ctSafe 4 demoMulZero demoK

/-- The composed pipeline is cost-non-increasing on the demo. -/
example : comCost (comAlgebraicPipeline 4 demoMulZero demoK) ≤ comCost demoMulZero :=
  comAlgebraicPipeline_cost_le 4 demoMulZero demoK

/-- The composed pipeline on the peephole demo (`x ↦ x - x`): the peephole
    half fires (`sub x x ↦ xor x x`), the saturation half leaves it
    (no known constant), and denotation is preserved (both map `x` to `0`). -/
example (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (comAlgebraicPipeline 4 demoSelfSub demoK).denote V = demoSelfSub.denote V :=
  comAlgebraicPipeline_denote 4 demoSelfSub demoK V (demoK_consistent V)

/-- Smoke check: the composition module builds and its obligations close. -/
theorem comPipeline_compiles : True := trivial

end CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline
