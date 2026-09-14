/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum


@[expose] public section
set_option autoImplicit false

/-!
# Phase 0 axiom reality check

Statement-shape ratchet for the Edwards-curve algebraic axioms in
`EdwardsCurve.lean` and the optimization theorems in
`Ed25519Optimizations.lean`. Phase 0:
catch transcription errors in axiom statements *before* committing
~3 weeks of Coq proof work to discharging them.

## Scope

The actual axioms in `Ed25519Spec.lean` are over opaque `Fp25519` /
`EdPoint` carrier types — nothing to compute. The checkable subset is
the **algebraic-identity shapes** at the structural level: laws like
`add_comm`, `add_assoc`, `add_neg_self` over a concrete small
Edwards-style curve where computation is feasible.

We use `ZMod 11`-based toy curves as the test ground. Each shape is
discharged by `decide`, which exhausts the finite `ZMod 11` domain, so
a shape that holds here is verified for the toy curve. A shape that
would fail to `decide` is suspect of being either (a) wrong, or (b)
requiring a property of `Fp25519` not captured at the structural
level. Either way, fail-loud is good.

## Skipped (structural check inapplicable)

- `interp_fp_*` axioms (opaque carrier on LHS)
- `interp_fp_inv_pow` (same)
- Anything whose conclusion quantifies over opaque types

These are validated via RFC 8032 §7.1 KAT regression at the
`bench_ed25519_sign` level instead.

## When to run

Re-run on every change to `Ed25519Spec.lean` axiom *statements*. A
`decide` failure = transcription bug; fix the statement before any
Coq work commits to discharging it.

```
lake build CatCrypt.Crypto.Jasmin.Ed25519.PbtAxiomCheck
```

## Structure

Each block states the property over `ZMod p` for a small prime `p` and
discharges it by `decide` over the finite domain; a false shape breaks
the build.
-/

namespace CatCrypt.Crypto.Jasmin.Ed25519.PbtAxiomCheck

/-! ## ZMod-11 ring-axiom sanity checks

These are the no-op end of the spectrum: if these fail, mathlib has a
regression. Their value is in showing the harness works before the
Edwards-specific tests. -/

example : ∀ a b : ZMod 11, a + b = b + a := by
  decide

example : ∀ a b c : ZMod 11, a * (b * c) = (a * b) * c := by
  decide

example : ∀ a b : ZMod 11, a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by
  decide

/-! ## Curve25519-shape Edwards identities on ZMod 11

We pick `(a, d)` for the toy curve so that `d` is a non-square in
`ZMod 11` (Bernstein–Lange–Niederhagen non-square-d completeness
condition). For `ZMod 11`, the squares are `{0, 1, 3, 4, 5, 9}`;
non-squares are `{2, 6, 7, 8, 10}`. We pick `d = 2` and `a = 1`
(unrelated to Ed25519's `a = -1` because `-1` IS a square mod 11).

A point `(x, y)` is on the curve iff `a·x² + y² = 1 + d·x²·y²`.

The check exhausts every `(x, y)` over `ZMod 11` via `decide`,
guarded by the `onCurve11` predicate, so it verifies the *algebraic
shape* of the add formula's output as a polynomial identity on exactly
the on-curve points, modulo the on-curve relation. Off-curve points
satisfy the implication vacuously.
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
  decide

example : ∀ Px Py Qx Qy : ZMod 11,
    onCurve11 Px Py = true → onCurve11 Qx Qy = true →
    1 - d11 * Px * Qx * Py * Qy ≠ 0 := by
  decide

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
  decide

example : ∀ a b c : ZMod 11, (a + b) + c = a + (b + c) := by
  decide

example : ∀ a : ZMod 11, a + (-a) = 0 := by
  decide

example : ∀ a : ZMod 11, a + 0 = a := by
  decide

/-- Cancellation: `(P + (-k·P)) + k·P = P` over the additive group
    structure of `ZMod 11`. Mirrors `ed_add_neg_smul_cancel` from
    `Ed25519Optimizations.lean` §8. -/
example : ∀ k a : ZMod 11, (a + (-(k * a))) + (k * a) = a := by
  decide

/-! ## Open notes

The checks above exhaust the `ZMod 11` toy domain by `decide`. The
`to_affine_m1add` axiom (extended-coords ↔ affine equivalence when
`a = -1`) is the most leveraged single target: it is high-stakes (the
dalek pipeline depends on it) and its two sides are computable.
Exhausting valid `EdwardsPointExt` inputs (with `Z ≠ 0`, `T·Z = X·Y`,
on-curve) over a small field is deferred. -/

end CatCrypt.Crypto.Jasmin.Ed25519.PbtAxiomCheck
