/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.CoordinateRingDedekind
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.AdicValuation


@[expose] public section
set_option autoImplicit false

/-!
# Divisors on the affine model of a Weierstrass curve

For a Weierstrass curve `W` over a field `F` whose coordinate ring is integrally
closed, `W.CoordinateRing` is a Dedekind domain
(`WeierstrassCurve.Affine.CoordinateRing.instIsDedekindDomain`). This unlocks
mathlib's height-one-spectrum machinery: the maximal ideals of `W.CoordinateRing`
are the affine closed points of the curve, and to each nonzero element of the
function field `W.FunctionField = Frac(W.CoordinateRing)` mathlib assigns an
integer order at every such point (`FractionalIdeal.count`).

This file packages those orders into the divisor group of the affine model.

## Main definitions

- `WeierstrassCurve.Affine.Div W` : the divisor group, the finitely-supported
  functions `HeightOneSpectrum W.CoordinateRing →₀ ℤ`. `Finsupp` supplies its
  `AddCommGroup` structure.
- `WeierstrassCurve.Affine.degree` : the sum of the coefficients of a divisor
  (unweighted; see the note on residue-degree weighting below), bundled as
  `degreeHom : Div W →+ ℤ`.
- `WeierstrassCurve.Affine.divisorOf` : the divisor `∑_v ord_v(f) • v` of a
  nonzero function `f : W.FunctionFieldˣ`, where `ord_v(f)` is the order of `f`
  at the closed point `v`. The finite support is
  `FractionalIdeal.finite_factors`. It is a group homomorphism from the
  multiplicative group `W.FunctionFieldˣ` to the additive group `Div W`
  (`divisorOf_one`, `divisorOf_mul`), bundled as `divisorOfHom`.

## Degree of a principal divisor

The classical degree-zero law for principal divisors — `deg (div f) = 0` — holds
on the *smooth projective* model, summing the residue-degree-weighted orders over
*all* places of the function field, including the places at infinity. It is the
product formula for the function field.

Over the **affine** height-one spectrum used here the places at infinity are
absent, and the degree of a principal divisor is **not** zero in general. Already
for `f` the image of a nonzero non-unit `r ∈ W.CoordinateRing`, every order
`ord_v(f) = FractionalIdeal.count _ v (r)` is nonnegative
(`FractionalIdeal.count_coe_nonneg`) and at least one is positive (the ideal
`(r)` is proper and nonzero, so has a prime factor), hence `degree (divisorOf f)
> 0`. So no affine-level `degree_divisorOf_eq_zero` is available or true; the
degree-zero statement lives on the projective compactification and requires a
function-field product formula that mathlib does not provide.

The `degree` defined here is the plain sum of coefficients. The divisor degree
that enters the product formula weights each `v` by the residue degree
`[κ(v) : F]`; that weighting is not needed for the homomorphism/finite-support
packaging and is omitted.
-/

open scoped nonZeroDivisors
open IsDedekindDomain FractionalIdeal

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)
  [IsIntegrallyClosed W.CoordinateRing]

/-- The divisor group of the affine model of `W`: finitely-supported integer
combinations of the closed points (height-one primes) of `W.CoordinateRing`. The
`AddCommGroup` structure is the one `Finsupp` carries. -/
abbrev Div : Type _ := HeightOneSpectrum W.CoordinateRing →₀ ℤ

/-- The degree of a divisor: the sum of its coefficients (unweighted). -/
def degree (D : Div W) : ℤ := D.sum fun _ n => n

omit [IsIntegrallyClosed W.CoordinateRing] in
@[simp] lemma degree_zero : degree W 0 = 0 := by simp [degree]

omit [IsIntegrallyClosed W.CoordinateRing] in
lemma degree_add (D₁ D₂ : Div W) :
    degree W (D₁ + D₂) = degree W D₁ + degree W D₂ := by
  simpa [degree] using
    Finsupp.sum_add_index' (h := fun _ (n : ℤ) => n) (fun _ => rfl) (fun _ _ _ => rfl)

/-- The degree map as an additive homomorphism `Div W →+ ℤ`. -/
def degreeHom : Div W →+ ℤ where
  toFun := degree W
  map_zero' := degree_zero W
  map_add' := degree_add W

omit [IsIntegrallyClosed W.CoordinateRing] in
@[simp] lemma degreeHom_apply (D : Div W) : degreeHom W D = degree W D := rfl

/-- The order of a nonzero function `f` at a closed point `v`: the multiplicity
of `v` in the factorization of the principal fractional ideal `(f)`. -/
noncomputable def ord (v : HeightOneSpectrum W.CoordinateRing)
    (f : W.FunctionFieldˣ) : ℤ :=
  FractionalIdeal.count W.FunctionField v
    (spanSingleton W.CoordinateRing⁰ (f : W.FunctionField))

/-- The principal divisor of a nonzero function `f`: `∑_v ord_v(f) • v`. The
support is finite by `FractionalIdeal.finite_factors`. -/
noncomputable def divisorOf (f : W.FunctionFieldˣ) : Div W :=
  Finsupp.ofSupportFinite (fun v => ord W v f) <| by
    have h := FractionalIdeal.finite_factors
      (spanSingleton W.CoordinateRing⁰ (f : W.FunctionField))
    simpa [Function.support, ord] using Filter.eventually_cofinite.mp h

@[simp] lemma divisorOf_apply (f : W.FunctionFieldˣ)
    (v : HeightOneSpectrum W.CoordinateRing) :
    divisorOf W f v = ord W v f :=
  rfl

/-- The order of a nonzero function at a point is additive in the function. -/
lemma ord_mul (v : HeightOneSpectrum W.CoordinateRing) (f g : W.FunctionFieldˣ) :
    ord W v (f * g) = ord W v f + ord W v g := by
  have hf : spanSingleton W.CoordinateRing⁰ (f : W.FunctionField) ≠ 0 := by
    rw [spanSingleton_ne_zero_iff]; exact Units.ne_zero f
  have hg : spanSingleton W.CoordinateRing⁰ (g : W.FunctionField) ≠ 0 := by
    rw [spanSingleton_ne_zero_iff]; exact Units.ne_zero g
  simp only [ord, Units.val_mul, ← spanSingleton_mul_spanSingleton]
  rw [FractionalIdeal.count_mul _ v hf hg]

@[simp] lemma ord_one (v : HeightOneSpectrum W.CoordinateRing) :
    ord W v (1 : W.FunctionFieldˣ) = 0 := by
  simp only [ord, Units.val_one, spanSingleton_one]
  exact FractionalIdeal.count_one _ v

@[simp] lemma divisorOf_one : divisorOf W (1 : W.FunctionFieldˣ) = 0 := by
  ext v; simp

lemma divisorOf_mul (f g : W.FunctionFieldˣ) :
    divisorOf W (f * g) = divisorOf W f + divisorOf W g := by
  ext v; simp [ord_mul]

/-- The principal-divisor map as a homomorphism from the multiplicative group of
nonzero functions to the additive divisor group. -/
noncomputable def divisorOfHom : Additive W.FunctionFieldˣ →+ Div W where
  toFun f := divisorOf W (Additive.toMul f)
  map_zero' := divisorOf_one W
  map_add' f g := divisorOf_mul W (Additive.toMul f) (Additive.toMul g)

@[simp] lemma divisorOfHom_apply (f : W.FunctionFieldˣ) :
    divisorOfHom W (Additive.ofMul f) = divisorOf W f :=
  rfl

end WeierstrassCurve.Affine
