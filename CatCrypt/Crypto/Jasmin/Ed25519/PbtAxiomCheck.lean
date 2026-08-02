/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Plausible

set_option autoImplicit false

/-!
# Phase 0 PBT reality check

Property-based-test ratchet for the Edwards-curve algebraic axioms in
`EdwardsCurve.lean` and the optimization theorems in
`Ed25519Optimizations.lean`. Phase 0:
catch transcription errors in axiom statements *before* committing
~3 weeks of Coq proof work to discharging them.

## Why this is limited

The actual axioms in `Ed25519Spec.lean` are over opaque `Fp25519` /
`EdPoint` carrier types — nothing to randomize. The PBT-applicable
subset is the **algebraic-identity shapes** at the structural level:
laws like `add_comm`, `add_assoc`, `add_neg_self` over a concrete
small Edwards-style curve where computation is feasible.

We use `ZMod 11`-based toy curves as the test ground. A property that
holds on `ZMod 11` but the real proof requires `Fp25519` is suspect
of being either (a) wrong, or (b) requiring a property of `Fp25519`
not yet captured in our axioms. Either way, fail-loud is good.

## Skipped (PBT inapplicable, per option-b-plan §0.2)

- `interp_fp_*` axioms (opaque carrier on LHS)
- `interp_fp_inv_pow` (same)
- Anything whose conclusion quantifies over opaque types

These are validated via RFC 8032 §7.1 KAT regression at the
`bench_ed25519_sign` level instead.

## When to run

Re-run on every change to `Ed25519Spec.lean` axiom *statements*. A
counterexample = transcription bug; fix the statement before any
Coq work commits to discharging it.

```
lake build CatCrypt.Crypto.Jasmin.Ed25519.PbtAxiomCheck
```

## Structure

Each test block:
1. Defines the property over `ZMod p` for a small prime `p`
2. Asserts via `example := by plausible (config := { numInst := 100 })`
3. If Plausible finds a counterexample, the file fails to build
-/

namespace CatCrypt.Crypto.Jasmin.Ed25519.PbtAxiomCheck

/-! ## Plausible instances for `ZMod 11`

`ZMod (n+1)` is definitionally `Fin (n+1)`, but instance search does
not unfold `ZMod` automatically. Provide explicit shims that delegate
to `Fin 11`'s `Arbitrary`/`Shrinkable`/`Repr` instances so we can use
`plausible` over `ZMod 11`. -/

instance : Plausible.Shrinkable (ZMod 11) where
  shrink _ := []

instance : Plausible.Arbitrary (ZMod 11) where
  arbitrary := do
    let m ← Plausible.Gen.choose Nat 0 10 (by omega)
    return (m : ZMod 11)

/-! ## ZMod-11 ring-axiom sanity checks

These are the no-op end of the spectrum: if these fail, mathlib has a
regression. Their value is in showing the harness works before the
Edwards-specific tests. -/

example : ∀ a b : ZMod 11, a + b = b + a := by
  plausible (config := { numInst := 100 })

example : ∀ a b c : ZMod 11, a * (b * c) = (a * b) * c := by
  plausible (config := { numInst := 100 })

example : ∀ a b : ZMod 11, a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by
  plausible (config := { numInst := 100 })

/-! ## Curve25519-shape Edwards identities on ZMod 11

We pick `(a, d)` for the toy curve so that `d` is a non-square in
`ZMod 11` (Bernstein–Lange–Niederhagen non-square-d completeness
condition). For `ZMod 11`, the squares are `{0, 1, 3, 4, 5, 9}`;
non-squares are `{2, 6, 7, 8, 10}`. We pick `d = 2` and `a = 1`
(unrelated to Ed25519's `a = -1` because `-1` IS a square mod 11).

A point `(x, y)` is on the curve iff `a·x² + y² = 1 + d·x²·y²`.

The PBT here doesn't search over actual on-curve points (rare for
random `(x, y)`). Instead it exercises the *algebraic shape* of the
add formula's output as a polynomial identity, modulo the on-curve
relation.

NOTE: Plausible's randomization may generate `(x, y)` not on-curve
in which case the property is vacuously true (the if-then implication
short-circuits). This means the "real" coverage is only on the few
random on-curve hits. For meaningful coverage, generate on-curve
points by parameterization (a,b,c,d → on-curve via Lange's formula
or by sampling y and computing the corresponding x via `sqrt(...)`).
-/

/-- Test data: `(a, d)` for our toy Edwards curve over `ZMod 11`. -/
def a11 : ZMod 11 := 1
def d11 : ZMod 11 := 2

/-- On-curve predicate (concrete, decidable). -/
def onCurve11 (x y : ZMod 11) : Bool :=
  decide (a11 * x^2 + y^2 = 1 + d11 * x^2 * y^2)

/-- Derived BLN denominators, proved in `EdwardsCurve.lean` as
    `add_denom_pos`/`add_denom_neg`. PBT check: for any `(Px, Py)`,
    `(Qx, Qy)` *both on-curve*, the denominators `1 ± d·Px·Qx·Py·Qy`
    are nonzero.

    This validates the *statement shape* of `add_denom_pos`/`_neg`
    (not the full Curve25519 case, since `ZMod 11`'s `d = 2` is the
    PBT-friendly proxy). -/
example : ∀ Px Py Qx Qy : ZMod 11,
    onCurve11 Px Py = true → onCurve11 Qx Qy = true →
    1 + d11 * Px * Qx * Py * Qy ≠ 0 := by
  plausible (config := { numInst := 1000 })

example : ∀ Px Py Qx Qy : ZMod 11,
    onCurve11 Px Py = true → onCurve11 Qx Qy = true →
    1 - d11 * Px * Qx * Py * Qy ≠ 0 := by
  plausible (config := { numInst := 1000 })

/-! ## Ed25519Optimizations.lean group-theory cascade

Most theorems in §6/§8 of `Ed25519Optimizations.lean` are derived from
`ed_add_comm`, `ed_add_assoc`, `ed_add_left_id`, `ed_smul_distrib_add`,
etc. — abstract group axioms over `EdPoint`. Since `EdPoint` is
axiomatic, we PBT-check the *shape* of the derivations on a concrete
abelian group.

Use `(ZMod 11, +)` as the test group (commutative, associative,
identity = 0, inverses = negation). The cascade theorems should hold
purely from group axioms, so they should PBT-pass without needing
curve-specific properties. -/

example : ∀ a b : ZMod 11, a + b = b + a := by
  plausible (config := { numInst := 100 })

example : ∀ a b c : ZMod 11, (a + b) + c = a + (b + c) := by
  plausible (config := { numInst := 100 })

example : ∀ a : ZMod 11, a + (-a) = 0 := by
  plausible (config := { numInst := 100 })

example : ∀ a : ZMod 11, a + 0 = a := by
  plausible (config := { numInst := 100 })

/-- Cancellation: `(P + (-k·P)) + k·P = P` over the additive group
    structure of `ZMod 11`. Mirrors `ed_add_neg_smul_cancel` from
    `Ed25519Optimizations.lean` §8. -/
example : ∀ k a : ZMod 11, (a + (-(k * a))) + (k * a) = a := by
  plausible (config := { numInst := 100 })

/-! ## Open notes

Tests above all have small numTests (100–1000). For real Phase 0 use
(running before each Coq Phase 1 sub-task), increase to 100,000+ on
the most-leveraged axioms. The tests run in <1s each at numTests=1000.

The `to_affine_m1add` axiom (extended-coords ↔ affine equivalence
when `a = -1`) is the most leveraged single PBT target: it's both
high-stakes (the dalek pipeline depends on it) and PBT-friendly
since both sides are computable. Generating valid `EdwardsPointExt`
inputs (with `Z ≠ 0`, `T·Z = X·Y`, on-curve) requires custom
sampleable instances, deferred. -/

end CatCrypt.Crypto.Jasmin.Ed25519.PbtAxiomCheck
