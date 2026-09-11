/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# ModArith Montgomery-domain inverse — the `mont_inverse` leaf

The Montgomery-domain field inverse and its correctness lemmas. The op it backs is
`ModArithOp.montInverse` in `ModArithDialect`; prime-ir calls it
`mod_arith.mont_inverse` (`ModArithOps.td`).

The op sits in `modArithDialect` rather than a dialect of its own, because a `Com`
carries ops from one dialect and an op alone in its dialect cannot appear beside
`modMul`. A coproduct with an injection (`VIR/DialectCoproduct.lean`) was the
alternative; folding was chosen because the value types already coincide at
`ZMod p`. `VIR/FoldedOpAgreement.lean` ties the folded op to `montInverseF` below.

## What the leaf computes

Per `PRIME_IR_OP_CORRESPONDENCE.md` (repo root, §2), CatCrypt already *has* the field
inverse — `ModArithDialect.byInverse` / `FieldDialect.fInv` denote to `ZMod p`'s
native `a⁻¹`, realised by the Bernstein–Yang / Fermat chains — but it does **not**
expose the *Montgomery-domain* inverse as a standalone op.  The gap analysis
classified `mod_arith.mont_inverse` **PARTIAL** — "Fermat chain in Montgomery
domain; no dedicated mont-inverse op".  This dialect **factors that map as a
first-class op**, matching prime-ir's `mod_arith.mont_inverse` one-for-one.

It is a **separate file** from the `to_mont`/`from_mont`/`mont_square` trio
(`ModArithMontOps.lean`) because that file carries residues as **ℤ** with the
`Int.ModEq` redc core, which has no total modular inversion; the inverse is clean
over the **`ZMod p`** carrier, where `⁻¹` is total and the Montgomery convention
is the one `ModArithDialect.montMul`/`montReduce` already fix.

## The Montgomery convention (reused from `ModArithDialect`)

`ModArithDialect.montMulF rInv a b = a · b · R⁻¹` and
`montReduceF rInv t = t · R⁻¹`, where `rInv = (R : ZMod p)⁻¹` is the
Montgomery-radix inverse.  A *residue* `x̃` is the Montgomery form of the logical
value `montReduce rInv x̃ = x̃ · R⁻¹`, and the Montgomery unit (the form of `1`) is
`R = rInv⁻¹`.

## The leaf, parametric in `(p, rInv)`

* `montInverse p rInv` — `x ↦ x⁻¹ · rInv⁻¹ · rInv⁻¹` (`= x⁻¹ · R²`, since
  `rInv⁻¹ = R`).  This is the residue whose Montgomery product with `x̃` is the
  unit `R`: `montMul rInv x̃ (montInverse x̃) = R`.  Equivalently, its logical value
  is the inverse of `x̃`'s logical value (`montInverse_fromMont`).

## Correctness lemmas (assembled from `ZMod`'s field inverse)

Over a prime modulus (`Fact (Nat.Prime p)`, giving `Field (ZMod p)`), with `x`
and `rInv` nonzero:

* `montInverse_spec` : `montMul rInv x (montInverse rInv x) = rInv⁻¹` — the
  Montgomery product with the inverse is the unit `R`.
* `montInverse_fromMont` : `(fromMont x) · (fromMont (montInverse x)) = 1` — the
  logical values are mutually inverse (the field-level statement).

## Constant-time

The Montgomery inverse is realised by a fixed Fermat / divstep schedule, whose
exponent and step count are public, so the leaf is a total pure function and the
folded op is constant-time on the `ModArithDialect.byInverse` story.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ModArithMontInverse

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect (montMulF montReduceF byInverseF)

/-! ## 1. The leaf function (the Montgomery-domain inverse)

`x ↦ x⁻¹ · rInv⁻¹ · rInv⁻¹` (= `x⁻¹ · R²`): the residue whose Montgomery product
with `x̃` is the unit `R = rInv⁻¹`.  Built from `ZMod p`'s native `⁻¹`. -/

/-- `mod_arith.mont_inverse` leaf: the Montgomery-domain inverse
    `x ↦ x⁻¹ · rInv⁻¹ · rInv⁻¹` over `ZMod p`, where `rInv = R⁻¹` is the
    Montgomery-radix inverse fixed by `ModArithDialect.montMul` (so `rInv⁻¹ = R`
    and the result is `x⁻¹ · R²`). -/
@[reducible] def montInverseF {p : Nat} (rInv x : ZMod p) : ZMod p :=
  x⁻¹ * rInv⁻¹ * rInv⁻¹

/-! ## 2. Correctness lemmas (assembled from `ZMod`'s native inverse)

Over a prime modulus the carrier is a field, so a nonzero residue is a unit and
`ZMod.mul_inv_of_unit` / `ZMod.inv_mul_of_unit` discharge the cancellations.  We
read the inverse through `ZMod.inv` (the instance `montInverseF` uses), so the
unit witness is built from Fermat's little theorem rather than the field's
`GroupWithZero` inverse, which lives behind a different instance. -/

/-- A nonzero residue at a prime modulus is a unit, witnessed by `x · x^(p-2) = 1`
    (Fermat).  Phrased over `ZMod`'s monoid so it feeds `ZMod.mul_inv_of_unit`. -/
theorem isUnit_of_ne_zero {p : Nat} [Fact (Nat.Prime p)] {a : ZMod p}
    (ha : a ≠ 0) : IsUnit a :=
  IsUnit.of_mul_eq_one (a ^ (p - 2)) <| by
    rw [← pow_succ', show (p - 2) + 1 = p - 1 from by
      have := (Fact.out : Nat.Prime p).two_le; omega]
    exact ZMod.pow_card_sub_one_eq_one ha

/-- **Montgomery-inverse spec.** The Montgomery product of `x̃` with its
    Montgomery inverse is the unit `R = rInv⁻¹`:
    `montMul rInv x (montInverse rInv x) = rInv⁻¹`. -/
theorem montInverse_spec {p : Nat} [Fact (Nat.Prime p)] (rInv x : ZMod p)
    (hx : x ≠ 0) (hr : rInv ≠ 0) :
    montMulF rInv x (montInverseF rInv x) = rInv⁻¹ := by
  unfold montMulF montInverseF
  have ex : x * x⁻¹ = 1 := ZMod.mul_inv_of_unit x (isUnit_of_ne_zero hx)
  have er : rInv⁻¹ * rInv = 1 := ZMod.inv_mul_of_unit rInv (isUnit_of_ne_zero hr)
  rw [show x * (x⁻¹ * rInv⁻¹ * rInv⁻¹) * rInv
        = (x * x⁻¹) * (rInv⁻¹ * rInv) * rInv⁻¹ by ring, ex, er, one_mul, one_mul]

/-- **Logical inverse domain.** The logical (out-of-Montgomery) values of `x̃` and
    of `montInverse x̃` are mutually inverse: `(fromMont x) · (fromMont (montInverse x)) = 1`,
    where `fromMont = montReduce rInv = · R⁻¹`. -/
theorem montInverse_fromMont {p : Nat} [Fact (Nat.Prime p)] (rInv x : ZMod p)
    (hx : x ≠ 0) (hr : rInv ≠ 0) :
    montReduceF rInv x * montReduceF rInv (montInverseF rInv x) = 1 := by
  unfold montReduceF montInverseF
  have ex : x * x⁻¹ = 1 := ZMod.mul_inv_of_unit x (isUnit_of_ne_zero hx)
  have emr : rInv * rInv⁻¹ = 1 := ZMod.mul_inv_of_unit rInv (isUnit_of_ne_zero hr)
  have er : rInv⁻¹ * rInv = 1 := ZMod.inv_mul_of_unit rInv (isUnit_of_ne_zero hr)
  rw [show x * rInv * (x⁻¹ * rInv⁻¹ * rInv⁻¹ * rInv)
        = (x * x⁻¹) * (rInv * rInv⁻¹) * (rInv⁻¹ * rInv) by ring,
    ex, emr, er, one_mul, one_mul]

