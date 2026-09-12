/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.Optimizer.Rewrite.Egraph
public import CatCrypt.Crypto.Optimizer.Rewrite.KaratsubaGenericPass
public import CatCrypt.Crypto.Optimizer.Rewrite.RegistryEgraphBridge

/-!
# `grind` as the congruence-closure discharger for the compiler e-graph

`Bridges/Transfer/GrindIntegration.lean` dual-tags Trocq's foundation realization
squares (`mul_repr : a * b = bbFieldMul a b`, …) `@[grind =]`, so `grind`'s
congruence closure composes the per-operation transport squares automatically and
discharges `transfer` leaf equations in one `grind` — no positional `rw` chain.

This file is the **same move for our equality-saturation optimizer**
(`Optimizer/Rewrite/Egraph.lean`). The optimizer's rewrite rules are themselves
denotation-preserving equations (`mul_one_eq : x * 1 = x`,
`mul_pow2_eq_shl : x * 2^k = x <<< k`, the annihilators, …), and the
algorithmic-refinement equations (`karatsubaMul_eq_schoolbook`) are denotation-
preserving equations over a generic ring. Dual-tagging them `@[grind =]` puts
them in `grind`'s database, after which a single `grind` discharges a *multi-rule
rewrite leaf* — the composite simplification the e-graph reaches over several
saturation passes — by congruence closure.

This is the concrete wiring behind the observation that **`grind` (proof-side),
our e-graph (`saturateCom`, program-side), and Trocq/`Related` (relation-side) are
the same congruence-closure construction**: `RegistryEgraphBridge` already showed
the e-graph rules and the `Related` rules share one *denotation-preserving
equation* representation; here that shared representation is fed to `grind`, so
`grind`'s congruence closure becomes a leaf-discharger / certifier for the e-graph
rule compositions, exactly as `GrindIntegration` made it for `transfer`. (Recall
`EgraphOracle.lean` already names a "`grind`-style heuristic" as a permissible
*untrusted* oracle backend; this is the *trusted* face — `grind` closing the
certificate, not driving the search.)

## Scope

- `grind` here **composes already-proven rules**; it does not re-derive their
  soundness. Each `*_eq` lemma carries its own proof (`simp` / `bv_decide`-style
  BitVec reasoning / `ring`); `grind` only chains the registered equations through
  congruence closure to close a composite. This is the leaf-discharge step, not a
  proof-producing saturation engine (extraction / cost-minimisation stays the
  unverified search; soundness is the rule-chain certificate, cf. `saturateCom_denote`).
- **Carrier caveat (from the Trocq note).** `grind` times out chasing `BitVec`
  *arithmetic chains*. It is safe here because the optimizer's rules are simple
  *collapse / annihilation / strength-reduction* identities (their RHS is `x`, `0`,
  or a single opaque `<<<`), and the refinement rules keep the ring ops abstract —
  `grind` composes the equations without descending into kernel arithmetic. Do not
  expect `grind` to *prove* an arithmetic-heavy rule's soundness (e.g.
  `mul_pow2_eq_shl`'s own `BitVec` proof stays `bv`-level); it composes that rule
  once proven.
-/

@[expose] public section

namespace CatCrypt.Crypto.Optimizer.Rewrite.EgraphGrindIntegration

open CatCrypt.Crypto.Optimizer.Rewrite

/-! ## 1. Dual-tag the optimizer's denotation-preserving rules for `grind`

The same equations the e-graph's `algebraicRules` carry as `*_sound` lemmas, also
tagged as `@[grind =]` rewrite candidates. `mul_one_eq` and `mul_zero_eq` carry
no tag: `grind` normalises a candidate's left-hand side before extracting its
E-matching pattern, and `x * 1` / `x * 0` normalise to `x` / `0` (`BitVec.mul_one`,
`BitVec.mul_zero`), which leaves no pattern; the two identities are applied by
that same normalisation. -/

attribute [grind =] Egraph.add_zero_eq
  Egraph.xor_zero_eq Egraph.or_zero_eq Egraph.and_zero_eq Egraph.mul_pow2_eq_shl
attribute [grind =] KaratsubaGeneric.karatsubaMul_eq_schoolbook

/-! ## 2. `grind` composes the collapse / annihilation rules (e-graph saturation in one shot)

Each goal below is a composite the e-graph reaches only by *several* saturation
passes; `grind` closes it in one, composing the registered squares. -/

/-- A nested collapse leaf: `((x·1)+0)·1 = x`. The e-graph needs three rewrites
    (`mul_one`, `add_zero`, `mul_one`); `grind` composes them via congruence closure. -/
theorem grind_collapse_leaf {w : Nat} (x : BitVec w) :
    ((x * (BitVec.ofNat w 1)) + (BitVec.ofNat w 0)) * (BitVec.ofNat w 1) = x := by
  grind

/-- Collapse mixed with annihilation: `((x·1) ^^^ 0) + (y·0) = x` — the
    `mul_zero` annihilator feeds `add_zero`, the `mul_one`/`xor_zero` collapse the
    left, all composed by `grind`. -/
theorem grind_annihilate_leaf {w : Nat} (x y : BitVec w) :
    ((x * (BitVec.ofNat w 1)) ^^^ (BitVec.ofNat w 0)) + (y * (BitVec.ofNat w 0)) = x := by
  grind

/-- Strength-reduction composed with collapse: `(x · 2^k) + 0 = x <<< k`. The
    cost-reducing `mul_pow2_eq_shl` rule and the `add_zero` collapse compose in one
    `grind` (the `<<<` on the RHS stays opaque — no `BitVec` arithmetic chase). -/
theorem grind_strength_reduce_leaf {w : Nat} (x : BitVec w) (k : Nat) :
    (x * (BitVec.ofNat w (2 ^ k))) + (BitVec.ofNat w 0) = x <<< k := by
  grind

/-! ## 3. `grind` composes the algorithmic-refinement rule (the field-transfer analogue)

`karatsubaMul_eq_schoolbook` is a `ring`-proved denotation-preserving equation over
a generic `CommRing R` (opaque ring ops — the optimizer analogue of the opaque
`bbField*` kernel ops in `GrindIntegration`). `grind` discharges it from the
database, exactly as it discharges a Trocq field-realization leaf. -/

/-- The Karatsuba refinement, discharged by `grind` from the database — the
    optimizer-side analogue of `GrindIntegration.grind_leaf`. -/
theorem grind_karatsuba_leaf {R : Type} [CommRing R] (B a1 a0 b1 b0 : R) :
    KaratsubaGeneric.karatsubaMul B a1 a0 b1 b0
      = KaratsubaGeneric.schoolbookMul B a1 a0 b1 b0 := by
  grind

end CatCrypt.Crypto.Optimizer.Rewrite.EgraphGrindIntegration
