/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.CurveDivisor
public import Mathlib.RingTheory.Valuation.ValuationSubring


@[expose] public section
set_option autoImplicit false

/-!
# Evaluation of a function at a closed point, and Weil reciprocity

For a Weierstrass curve `W` whose coordinate ring is a Dedekind domain
(`CurveDivisor.lean`), a nonzero function `f : W.FunctionFieldˣ` has a value in
the residue field `κ(v)` at every closed point `v` where it is regular and
nonvanishing — that is, at every `v` outside the support of `divisorOf f`. This
file packages that residue-field evaluation and states where Weil reciprocity
`f(div g) = g(div f)` sits relative to mathlib.

## Function-at-a-point evaluation

At a closed point `v` (a height-one prime of `W.CoordinateRing`) mathlib's
`IsDedekindDomain.HeightOneSpectrum.valuation` gives a valuation
`v.valuation : Valuation W.FunctionField ℤᵐ⁰`, whose valuation subring `𝒪_v`
(`Valuation.valuationSubring`) is the local ring of `v`. Its unit group
`(𝒪_v).unitGroup` is the multiplicative group of functions with valuation `1`
at `v` — the functions that are regular and nonvanishing at `v`, equivalently
`ord_v f = 0` (`v ∉ supp (divisorOf f)`). The residue field is
`κ(v) = IsLocalRing.ResidueField 𝒪_v`, and mathlib's
`ValuationSubring.unitGroupToResidueFieldUnits` sends a `v`-adic unit to its
value `f(v) ∈ κ(v)ˣ`.

- `WeierstrassCurve.Affine.residueFieldAt W v` : the residue field `κ(v)`.
- `WeierstrassCurve.Affine.evalHom W v` : the group homomorphism
  `(𝒪_v).unitGroup →* κ(v)ˣ` evaluating a `v`-adic unit at `v`.
- `WeierstrassCurve.Affine.evalAt W v f` : the value `f(v) ∈ κ(v)ˣ` of a
  `v`-adic unit `f`, with `evalAt_one` and `evalAt_mul`.

The input to `evalAt` is a member of `(𝒪_v).unitGroup`, i.e. a proof
`(𝒪_v).valuation f = 1`. This is the analytic form of the disjointness
condition `ord_v f = 0`. Identifying the two — `f ∈ (𝒪_v).unitGroup ↔
ord W v f = 0`, where `ord` is the `FractionalIdeal.count` order of
`CurveDivisor.lean` — is a `count`-versus-`valuation` bridge that mathlib does
not provide as a lemma; see the note below.

## Weil reciprocity is projective, and its ingredients are not in mathlib

Weil reciprocity states `f(div g) = g(div f)` for `f g : W.FunctionFieldˣ`,
where `f(div g) = ∏_v N_{κ(v)/F}(f(v))^{ord_v g}` pairs one function against the
principal divisor of the other. It is equivalent to the vanishing of the sum of
local tame symbols over **all** places of the function field:
`∏_v (f, g)_v = 1`, with `(f, g)_v = (-1)^{ord_v f · ord_v g}
(f^{ord_v g} / g^{ord_v f})(v) ∈ κ(v)ˣ`.

This does not compose from mathlib. The missing pieces are:

1. **No tame symbol.** mathlib has no `tameSymbol`. The local symbol `(f, g)_v`
   can be built from `evalHom` (the combination `f^{ord_v g} · g^{-ord_v f}` has
   valuation `1` at `v`, so it evaluates in `κ(v)ˣ`), but this is not packaged
   upstream.

2. **No function-field product formula.** The reciprocity identity
   `∏_v (f, g)_v = 1` is a product formula over all places. mathlib has the
   product formula only for global fields with archimedean places
   (`NumberField.FinitePlace.prod_abs_eq_one`,
   `Mathlib.NumberTheory.Height.Basic.product_formula`); there is no
   function-field analogue, and no `∑_v ord_v = 0` place-sum lemma for a
   function field.

3. **No residue-degree norm to the base field.** Assembling the per-place values
   `f(v) ∈ κ(v)ˣ` into a single `F`-valued pairing needs the norm
   `N_{κ(v)/F} : κ(v)ˣ →* Fˣ`, which needs `κ(v)/F` finite; mathlib does not
   provide the residue field of a closed point of `W` as a finite `F`-algebra.

4. **No `count`-versus-`valuation` bridge.** Relating `ord W v f = 0` (the
   `FractionalIdeal.count` order of `CurveDivisor.lean`) to
   `f ∈ (𝒪_v).unitGroup` (`v.valuation f = 1`) is not a mathlib lemma.

Moreover, like the degree-zero law for principal divisors, reciprocity is a
statement about the **smooth projective** model: the product `∏_v (f, g)_v` runs
over all places, including the places at infinity that the affine height-one
spectrum used here omits. The `CurveDivisor.lean` note records that over the
affine spectrum `deg (div f) ≠ 0` in general; for the same reason the affine
product `∏_{v affine} (f, g)_v` is not `1` in general, and no affine-level
reciprocity is available or true. Reciprocity lives on the projective
compactification and requires the function-field product formula.

This file therefore provides the regular-nonvanishing evaluation `evalAt` and
records the reciprocity target and its named gaps, rather than proving a false
affine statement.
-/

open scoped nonZeroDivisors
open IsDedekindDomain

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)
  [IsIntegrallyClosed W.CoordinateRing]

/-- The local ring `𝒪_v` at a closed point `v`: the valuation subring of the
`v`-adic valuation on `W.FunctionField`. Its unit group is the functions
regular and nonvanishing at `v` (`ord_v f = 0`). -/
noncomputable abbrev valuationSubringAt
    (v : HeightOneSpectrum W.CoordinateRing) : ValuationSubring W.FunctionField :=
  (HeightOneSpectrum.valuation W.FunctionField v).valuationSubring

/-- The residue field `κ(v)` at a closed point `v`. -/
noncomputable abbrev residueFieldAt
    (v : HeightOneSpectrum W.CoordinateRing) : Type _ :=
  IsLocalRing.ResidueField (valuationSubringAt W v)

/-- Evaluation at a closed point `v`, as a homomorphism from the group of
functions regular and nonvanishing at `v` to the multiplicative group of the
residue field: `f ↦ f(v)`. -/
noncomputable def evalHom (v : HeightOneSpectrum W.CoordinateRing) :
    (valuationSubringAt W v).unitGroup →* (residueFieldAt W v)ˣ :=
  (valuationSubringAt W v).unitGroupToResidueFieldUnits

/-- The value `f(v) ∈ κ(v)ˣ` of a function `f` that is regular and nonvanishing
at the closed point `v` (a member of `(𝒪_v).unitGroup`, i.e. `ord_v f = 0`). -/
noncomputable def evalAt (v : HeightOneSpectrum W.CoordinateRing)
    (f : (valuationSubringAt W v).unitGroup) : (residueFieldAt W v)ˣ :=
  evalHom W v f

@[simp] lemma evalAt_one (v : HeightOneSpectrum W.CoordinateRing) :
    evalAt W v 1 = 1 :=
  map_one (evalHom W v)

@[simp] lemma evalAt_mul (v : HeightOneSpectrum W.CoordinateRing)
    (f g : (valuationSubringAt W v).unitGroup) :
    evalAt W v (f * g) = evalAt W v f * evalAt W v g :=
  map_mul (evalHom W v) f g

end WeierstrassCurve.Affine
