/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.AdjoinRoot
public import CatCrypt.Crypto.Optimizer.Lattice.PolyConvGeneric

/-!
# Negacyclic convolution / NTT for `R[X]/(Xⁿ+1)` (generic `CommRing`)

This file gives the *generic spec* that an NTT-based multiply in the
ML-KEM / ML-DSA setting implements: multiplication in the **negacyclic** ring
`R[X]/(Xⁿ + 1)`, represented by low-first coefficient lists over a `CommRing R`.

In `R[X]/(Xⁿ + 1)` we have `Xⁿ = -1`, so the ordinary convolution of two
coefficient lists wraps around with a **sign flip**: the coefficient `k` of the
negacyclic product is

  `(∑_{i+j=k} aᵢ·bⱼ) − (∑_{i+j=k+n} aᵢ·bⱼ)`,

the second sum being the wrapped-around tail that picks up the `Xⁿ = -1` factor.
This is the heart of ML-KEM (`X²⁵⁶ + 1`) and ML-DSA (`X²⁵⁶ + 1`).

## Design

Rather than reason about the explicit sign-flip coefficient formula directly, we
anchor the spec in Mathlib. `Xⁿ + 1` is **monic** (for `n ≥ 1`), so reduction
modulo it is `Polynomial.modByMonic` (`%ₘ`). We define

* `negaModulus n` — the monic polynomial `Xⁿ + 1`;
* `negaConv a b n` — the coefficient list of `(toPoly a * toPoly b) %ₘ (Xⁿ+1)`;
* `toQuot n` — the image of a coefficient list in the quotient ring
  `AdjoinRoot (Xⁿ+1)` (i.e. `R[X]/(Xⁿ+1)`).

The keystone

  `negaConv_eq_mul : toQuot n (negaConv a b n) = toQuot n a * toQuot n b`

says `negaConv` *is* multiplication in `R[X]/(Xⁿ+1)`. It follows because passing
through `%ₘ (Xⁿ+1)` does not change the class modulo `Xⁿ+1`, and the convolution
spec `toPoly_conv` already gives `toPoly (conv a b) = toPoly a * toPoly b`.

The explicit sign-flip interpretation is recorded as the worked example `n = 2`:
`(1 + X)² = 2X` in `R[X]/(X²+1)` (since `X² = -1`, the `X²` term flips to `-1`
and cancels the constant `1`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.NegacyclicNTTGeneric

open Polynomial
open CatCrypt.Crypto.Optimizer.Lattice.PolyConvGeneric

variable {R : Type*} [CommRing R]

/-- The negacyclic modulus `Xⁿ + 1`, the defining polynomial of the ML-KEM /
ML-DSA ring `R[X]/(Xⁿ+1)`. -/
noncomputable def negaModulus (n : ℕ) : Polynomial R :=
  Polynomial.X ^ n + 1

/-- `Xⁿ + 1` is monic for `n ≥ 1`: its leading term is `Xⁿ` and the `+1` has
strictly smaller degree, so reduction modulo it is `modByMonic`. -/
theorem negaModulus_monic (n : ℕ) (hn : 0 < n) :
    (negaModulus n : Polynomial R).Monic := by
  unfold negaModulus
  apply Polynomial.monic_X_pow_add
  calc (1 : Polynomial R).degree ≤ 0 := Polynomial.degree_one_le
    _ < (n : WithBot ℕ) := by exact_mod_cast hn

/-- The **negacyclic convolution** of two low-first coefficient lists, as a
coefficient list. It is the ordinary convolution reduced modulo `Xⁿ + 1`:
`negaConv a b n = coeffs ((toPoly a * toPoly b) %ₘ (Xⁿ+1))`. Concretely the
coefficient `k` is `(∑_{i+j=k} aᵢbⱼ) − (∑_{i+j=k+n} aᵢbⱼ)` — the wrapped tail
flips sign because `Xⁿ = -1` in the quotient. -/
noncomputable def negaConv (a b : List R) (n : ℕ) : List R :=
  let P := (toPoly a * toPoly b) %ₘ (negaModulus n)
  (List.range (P.natDegree + 1)).map P.coeff

/-- `toPoly` of a `negaConv` list recovers the reduced product polynomial:
`toPoly (negaConv a b n) = (toPoly a * toPoly b) %ₘ (Xⁿ+1)`. This is the
list-level statement that `negaConv` performs the polynomial reduction. -/
theorem toPoly_negaConv (a b : List R) (n : ℕ) :
    toPoly (negaConv a b n) = (toPoly a * toPoly b) %ₘ (negaModulus n) := by
  unfold negaConv
  simp only []
  rw [toPoly_coeffList]

/-- The quotient ring `R[X]/(Xⁿ+1)` — the ML-KEM / ML-DSA coefficient ring. -/
abbrev NegaQuot (R : Type*) [CommRing R] (n : ℕ) : Type _ :=
  AdjoinRoot (negaModulus (R := R) n)

/-- The image of a coefficient list in the quotient ring `R[X]/(Xⁿ+1)`. -/
noncomputable def toQuot (n : ℕ) (l : List R) : NegaQuot R n :=
  AdjoinRoot.mk (negaModulus n) (toPoly l)

/-- **Keystone (quotient-ring multiplication).** The negacyclic convolution is
multiplication in `R[X]/(Xⁿ+1)`:

  `toQuot n (negaConv a b n) = toQuot n a * toQuot n b`.

This is the spec a negacyclic NTT-based multiply implements: the NTT multiplies
pointwise in the evaluation domain and interpolates back, computing exactly the
product in the quotient ring. The proof: `negaConv` reduces the ordinary product
modulo `Xⁿ+1`, and passing through `%ₘ (Xⁿ+1)` does not change the residue
class, so the quotient image is the product of the two quotient images. -/
theorem negaConv_eq_mul (a b : List R) (n : ℕ) :
    toQuot n (negaConv a b n) = toQuot n a * toQuot n b := by
  unfold toQuot
  rw [toPoly_negaConv, ← map_mul]
  rw [AdjoinRoot.mk_eq_mk]
  -- `f ∣ (P %ₘ f) - P`, since `P %ₘ f - P = f * (-(P /ₘ f))`.
  refine ⟨-((toPoly a * toPoly b) /ₘ (negaModulus n)), ?_⟩
  have h := Polynomial.modByMonic_add_div (toPoly a * toPoly b) (negaModulus n)
  linear_combination h

/-- Worked example over `ℤ`, `n = 2`: `(1 + X)² = 2X` in `ℤ[X]/(X²+1)`.
Since `X² = -1`, the `X²` coefficient `1` of `(1+X)² = 1 + 2X + X²` flips sign
and cancels the constant `1`, leaving `2X`. The negacyclic convolution of
`[1, 1]` with `[1, 1]` is therefore (as a class) `[0, 2]`. -/
example : toQuot 2 (negaConv ([1, 1] : List ℤ) [1, 1] 2)
    = toQuot 2 ([0, 2] : List ℤ) := by
  rw [negaConv_eq_mul]
  unfold toQuot
  rw [← map_mul, AdjoinRoot.mk_eq_mk]
  -- `(toPoly [1,1])² - toPoly [0,2] = (X²+1) * 1`, so it is divisible.
  refine ⟨1, ?_⟩
  simp [toPoly, negaModulus]
  ring

end CatCrypt.Crypto.Optimizer.Lattice.NegacyclicNTTGeneric
