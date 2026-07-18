/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCT

set_option autoImplicit false

/-!
# `LeafOps`: Per-curve modulus-parametric leaf operations

Phase E.1 (2026-05-04). Phase E added the modulus-parametric tower
constructors `TFpGen (modulusName : String) (byteSize : Nat)` and
`TFp2Gen` to `TowerType`. This file provides the matching operational
layer: a `LeafOps` typeclass parameterised by `modulusName : String`
that exposes the per-curve leaf operations used by inline arithmetic
emitters.

Each curve provides its own instance giving the leaf-function names
that should appear in the emitted `LowCT.RCall` constructors. The
typeclass is keyed on the same `String` modulus name carried by
`TFpGen`, so generic Lean code can dispatch the correct curve by
threading the modulus name through type-class resolution.

## Provided instances

| Modulus name  | Leaf prefix   | Notes                          |
|---------------|---------------|--------------------------------|
| `"Curve25519"`| `fp25519_*`   | RFC 7748 prime field           |
| `"P-256"`     | `fpP256_*`    | NIST P-256 prime field         |
| `"BLS12-381"` | `fp_*`        | BLS12-381 base prime field     |

Operations: `add`, `sub`, `mul`, `square`, `inv`, `neg`, `setZero`,
`setOne`, `copy`. Each produces a single `LowCT` (an `RCall` to the
corresponding leaf function).

## References

* `LowCT.lean` §1 — the `TowerType.TFpGen` / `TFp2Gen` constructors
* `LeafSig.lean` — leaf function signatures referenced by these calls
-/

namespace CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1  The `LeafOps` typeclass -/

/-- Per-curve leaf-operation interface, keyed by the curve's modulus
    name (the same `String` that parameterises `TowerType.TFpGen`).
    Each method builds the `LowCT` that calls the curve's named
    leaf function with the appropriate destination/argument layout. -/
class LeafOps (modulusName : String) where
  /-- `out := a + b` in the curve's base field. -/
  add     (out a b : Located) : LowCT
  /-- `out := a - b` in the curve's base field. -/
  sub     (out a b : Located) : LowCT
  /-- `out := a * b` in the curve's base field. -/
  mul     (out a b : Located) : LowCT
  /-- `out := a * a` in the curve's base field. -/
  square  (out a : Located) : LowCT
  /-- `out := a⁻¹` in the curve's base field. -/
  inv     (out a : Located) : LowCT
  /-- `out := -a` in the curve's base field. -/
  neg     (out a : Located) : LowCT
  /-- `out := 0` in the curve's base field. -/
  setZero (out : Located) : LowCT
  /-- `out := 1` in the curve's base field. -/
  setOne  (out : Located) : LowCT
  /-- `out := a` (copy/assignment in the curve's base field). -/
  copy    (out a : Located) : LowCT

/-! ## §2  Per-curve instances -/

/-- Curve25519 base-field leaf operations. Leaf names follow the
    `fp25519_*` convention used by the inline Curve25519 arithmetic
    emitter (`Curve25519Inline.lean`). -/
instance : LeafOps "Curve25519" where
  add     out a b := .RCall "fp25519_add"      out [a, b]
  sub     out a b := .RCall "fp25519_sub"      out [a, b]
  mul     out a b := .RCall "fp25519_mul"      out [a, b]
  square  out a   := .RCall "fp25519_square"   out [a]
  inv     out a   := .RCall "fp25519_inv"      out [a]
  neg     out a   := .RCall "fp25519_neg"      out [a]
  setZero out     := .RCall "fp25519_set_zero" out []
  setOne  out     := .RCall "fp25519_set_one"  out []
  copy    out a   := .RCall "fp25519_copy"     out [a]

/-- NIST P-256 base-field leaf operations. Leaf names follow the
    `fpP256_*` convention. -/
instance : LeafOps "P-256" where
  add     out a b := .RCall "fpP256_add"      out [a, b]
  sub     out a b := .RCall "fpP256_sub"      out [a, b]
  mul     out a b := .RCall "fpP256_mul"      out [a, b]
  square  out a   := .RCall "fpP256_square"   out [a]
  inv     out a   := .RCall "fpP256_inv"      out [a]
  neg     out a   := .RCall "fpP256_neg"      out [a]
  setZero out     := .RCall "fpP256_set_zero" out []
  setOne  out     := .RCall "fpP256_set_one"  out []
  copy    out a   := .RCall "fpP256_copy"     out [a]

/-- BLS12-381 base-field leaf operations. Leaf names use the bare
    `fp_*` convention historically used by the BLS12-381 inline
    emitter (this is the original, unparameterised tower). -/
instance : LeafOps "BLS12-381" where
  add     out a b := .RCall "fp_add"      out [a, b]
  sub     out a b := .RCall "fp_sub"      out [a, b]
  mul     out a b := .RCall "fp_mul"      out [a, b]
  square  out a   := .RCall "fp_square"   out [a]
  inv     out a   := .RCall "fp_inv"      out [a]
  neg     out a   := .RCall "fp_neg"      out [a]
  setZero out     := .RCall "fp_set_zero" out []
  setOne  out     := .RCall "fp_set_one"  out []
  copy    out a   := .RCall "fp_copy"     out [a]

/-! ## §3  Smoke tests

These `example`s pin the dispatch behaviour: invoking
`LeafOps.add (modulusName := …)` on each registered curve must
produce the expected `RCall` shape with the curve's leaf name and a
two-element argument list. -/

section SmokeTests

/-- Sample destination and source `Located`s used by the smoke tests
    below.  The `TowerType` chosen here is irrelevant — the smoke test
    only exercises the leaf-name dispatch. -/
private def smokeOut : Located := { locVar := "out", locSrc := .TFp }
private def smokeA   : Located := { locVar := "a",   locSrc := .TFp }
private def smokeB   : Located := { locVar := "b",   locSrc := .TFp }

/-- Curve25519 dispatch sanity check: `LeafOps.add` on Curve25519
    produces an `RCall` to `fp25519_add` with `out` as destination
    and `[a, b]` as arguments. -/
example :
    LeafOps.add (modulusName := "Curve25519") smokeOut smokeA smokeB
      = .RCall "fp25519_add" smokeOut [smokeA, smokeB] := rfl

/-- P-256 dispatch sanity check. -/
example :
    LeafOps.mul (modulusName := "P-256") smokeOut smokeA smokeB
      = .RCall "fpP256_mul" smokeOut [smokeA, smokeB] := rfl

/-- BLS12-381 dispatch sanity check. -/
example :
    LeafOps.square (modulusName := "BLS12-381") smokeOut smokeA
      = .RCall "fp_square" smokeOut [smokeA] := rfl

/-- Nullary-input dispatch (`setZero` / `setOne`): the leaf is called
    with the destination only and an empty argument list. -/
example :
    LeafOps.setZero (modulusName := "Curve25519") smokeOut
      = .RCall "fp25519_set_zero" smokeOut [] := rfl

example :
    LeafOps.setOne (modulusName := "P-256") smokeOut
      = .RCall "fpP256_set_one" smokeOut [] := rfl

/-- `copy` is a 1-input call: `out := a`. -/
example :
    LeafOps.copy (modulusName := "BLS12-381") smokeOut smokeA
      = .RCall "fp_copy" smokeOut [smokeA] := rfl

end SmokeTests

end CatCrypt.Crypto.Jasmin.LowCT
